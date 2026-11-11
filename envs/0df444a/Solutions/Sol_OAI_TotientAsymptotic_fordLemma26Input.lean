-- Prove2me | solution 1 for OAI.TotientAsymptotic.fordLemma26Input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:04.600211+00:00
-- url     : https://prove2.me/submissions/c37af2f9-c0ad-46c7-8199-244920c57940

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_cofactor_sieve_cutoff_mass

section
-- module Solutions.OAIQ233_TA.IEANTN_Mertens
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace Mertens



open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all <;> linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring



theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp <;> linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all <;> linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    all_goals try with_reducible_and_instances rfl
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast <;> ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all <;> linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast <;> linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    all_goals try with_reducible_and_instances rfl
    simp

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

end Mertens
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityIntervals
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity and prime-removal bridges for the normality intervals. -/
noncomputable section
namespace TotientAsymptotic

lemma omegaIn_mono (n : ℕ) {U₁ U₂ T₁ T₂ : ℝ} (hU : U₂≤U₁) (hT : T₁≤T₂) :
    omegaIn n U₁ T₁ ≤ omegaIn n U₂ T₂ := by
  classical
  unfold omegaIn
  rw [← List.countP_eq_length_filter,← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro p _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  exact ⟨hU.trans_lt hp.1,hp.2.trans hT⟩

lemma omegaIn_prime_le_one {p : ℕ} (hp : p.Prime) (U T : ℝ) :
    omegaIn p U T≤1 := by
  unfold omegaIn
  rw [Nat.primeFactorsList_prime hp]
  exact (List.length_filter_le _ _).trans (by simp)

lemma omegaIn_remove_prime {b q : ℕ} (hb : b≠0) (hq : q.Prime) (U T : ℝ) :
    omegaIn b U T ≤ omegaIn (b*q) U T ∧
      omegaIn (b*q) U T ≤ omegaIn b U T+1 := by
  rw [omegaIn_mul hb hq.ne_zero]
  have hh := omegaIn_prime_le_one hq U T
  omega

lemma prime_removal_deviation {b q : ℕ} (hb : b≠0) (hq : q.Prime)
    (U T M H : ℝ) (hbad : H≤|(omegaIn (b*q) U T:ℝ)-M|) :
    H-1≤|(omegaIn b U T:ℝ)-M| := by
  have hdiff := omegaIn_remove_prime hb hq U T
  have hl : (omegaIn b U T:ℝ)≤omegaIn (b*q) U T := by exact_mod_cast hdiff.1
  have hu : (omegaIn (b*q) U T:ℝ)≤(omegaIn b U T:ℝ)+1 := by exact_mod_cast hdiff.2
  have hab : |(omegaIn (b*q) U T:ℝ)-(omegaIn b U T:ℝ)|≤1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have htri := abs_sub_le (omegaIn (b*q) U T:ℝ) (omegaIn b U T:ℝ) M
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact double-logarithmic grid for reducing normality to finitely many intervals. -/
noncomputable section
namespace TotientAsymptotic

lemma normalityGridPoint_B (j : ℕ) : B (normalityGridPoint j) = j := by
  simp [normalityGridPoint,B]

lemma normalityGridPoint_mono : StrictMono normalityGridPoint := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  apply Real.exp_lt_exp.mpr
  exact_mod_cast hij

lemma normalityGridPoint_one_lt (j : ℕ) : 1<normalityGridPoint j :=
  Real.one_lt_exp_iff.mpr (Real.exp_pos _)

lemma normalityGridPoint_bracket {x : ℝ} (hx : 1<x) (hB : 0≤B x) :
    normalityGridPoint ⌊B x⌋₊ ≤ x ∧ x < normalityGridPoint (⌊B x⌋₊+1) := by
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have he : Real.exp (Real.exp (B x))=x := by
    simp only [B,Real.exp_log hlog,Real.exp_log hx0]
  constructor
  · calc
      _ ≤ Real.exp (Real.exp (B x)) := by
        apply Real.exp_le_exp.mpr
        apply Real.exp_le_exp.mpr
        exact Nat.floor_le hB
      _ = x := he
  · calc
      x = Real.exp (Real.exp (B x)) := he.symm
      _ < _ := by
        apply Real.exp_lt_exp.mpr
        apply Real.exp_lt_exp.mpr
        simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (B x)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridEnvelope
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common integer endpoint for every interval in the normality grid. -/
noncomputable section
namespace TotientAsymptotic

lemma normalityGridEnvelope_bounds {x : ℝ} (hx : Real.exp 1 ≤ x) :
    x ≤ normalityGridEnvelope x ∧ 2 ≤ normalityGridEnvelope x ∧
    normalityGridPoint (⌊B x⌋₊+1) ≤ normalityGridEnvelope x ∧
    Real.log (normalityGridEnvelope x) ≤ (Real.exp 1+1)*Real.log x := by
  have hx0 : 0<x := (Real.exp_pos _).trans_le hx
  have hx1 : 1<x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hB : 0 ≤ B x := Real.log_nonneg hlog
  let Y := normalityGridPoint (⌊B x⌋₊+1)
  have hY : 1<Y := normalityGridPoint_one_lt _
  have hceil : Y≤normalityGridEnvelope x := Nat.le_ceil Y
  have hNx : x≤normalityGridEnvelope x := (normalityGridPoint_bracket hx1 hB).2.le.trans hceil
  have hN2 : 2 ≤ normalityGridEnvelope x := by
    have htwo : (2:ℝ)≤Y := by
      have h1 := Real.one_le_exp (show (0:ℝ) ≤ ((⌊B x⌋₊+1:ℕ):ℝ) by positivity)
      have h2 := Real.add_one_le_exp (Real.exp ((⌊B x⌋₊+1:ℕ):ℝ))
      dsimp [Y,normalityGridPoint]
      linarith
    exact_mod_cast htwo.trans hceil
  have hN0 : (0:ℝ)<normalityGridEnvelope x := by exact_mod_cast (show 0<normalityGridEnvelope x by omega)
  have hupper : (normalityGridEnvelope x:ℝ)≤2*Y := by
    have hh := Nat.ceil_lt_add_one (le_of_lt (zero_lt_one.trans hY))
    dsimp [normalityGridEnvelope,Y] at *
    linarith
  have hinner : Real.exp (((⌊B x⌋₊+1:ℕ):ℝ)) ≤ Real.exp 1*Real.log x := by
    calc
      _ ≤ Real.exp (B x+1) := by
        apply Real.exp_le_exp.mpr
        push_cast
        linarith [Nat.floor_le hB]
      _ = _ := by rw [Real.exp_add]; simp only [B,Real.exp_log (by linarith : 0<Real.log x)] <;> ring
  have hlog2 : Real.log (2:ℝ)≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  refine ⟨hNx,hN2,hceil,?_⟩
  calc
    _ ≤ Real.log (2*Y) := Real.log_le_log hN0 hupper
    _ = Real.log 2+Real.exp (((⌊B x⌋₊+1:ℕ):ℝ)) := by
      rw [Real.log_mul (by norm_num) (by linarith : Y≠0)]
      simp only [Y,normalityGridPoint,Real.log_exp]
    _ ≤ _ := by nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The comparison of the exact Ford band centers with the phase-dependent
centers in the manuscript, equation `alpha-comparison`.  The ratio is
independent of the retained prime index, so its convergence gives a
uniform comparison over all indices below `m`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_ratio_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (p : ℝ)/(p-1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p-1 : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have he := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  push_cast at he
  have he' : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      n*(∏ p ∈ n.primeFactors, (p-1 : ℝ)) := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [Finset.prod_div_distrib]
  exact (div_eq_div_iff hφ.ne' hprod.ne').mpr (by nlinarith [he'])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedNormality
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ford, The distribution of totients, revised arXiv:1104.3264v2 (2013),
Lemma 2.6, p. 9. The author-hosted PDF states uniformity for x > 3 and
S > 2: https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf .
Only this count of exceptional primes is assumed. Reciprocal-weight and
actual good-witness discard estimates are derived separately.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma normal_two {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) : IsNormalPrime S 2 := by
  refine ⟨Nat.prime_two,?_,?_⟩
  · simp only [show (2 : ℕ)-1=1 from rfl,omegaIn,Nat.primeFactorsList_one,List.filter_nil,
      List.length_nil,Nat.cast_zero]
    linarith
  · intro U T hSU hUT hT
    norm_num at hT
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CanceledPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal cost of fixing the canceled primes, from Mertens' input. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeEulerProduct_pos (N : ℕ) : 0 < primeEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaReciprocal
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Euler-product moment for the remaining-factor exclusion.
The exponent three is sufficient for the application. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omegaReciprocal_nonneg (n : ℕ) : 0 ≤ omegaReciprocal n := by
  change 0 ≤ (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
  positivity

lemma omegaReciprocal_prime {p : ℕ} (hp : p.Prime) : omegaReciprocal p=(3/2 : ℝ)/p := by
  simp [omegaReciprocal,Nat.primeFactorsList_prime hp]

lemma omegaReciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖omegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p),omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma omega_euler_factor_le {p : ℕ} (hp : p.Prime) :
    (1-omegaReciprocal p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  rw [omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have ht : (0 : ℝ) < p-3/2 := by linarith
  have he : (1-(3/2 : ℝ)/(p : ℝ))⁻¹=(p : ℝ)/(p-3/2) := by field_simp
  rw [he,div_pow]
  apply (div_le_div_iff₀ ht (pow_pos hs 3)).mpr
  nlinarith [sq_nonneg ((p : ℝ)-2)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalOmegaMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative moments for the number of prime factors in an interval. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma intervalOmegaWeight_nonneg {a : ℝ} (ha : 0≤a) (U T : ℝ) (n : ℕ) :
    0 ≤ intervalOmegaWeight a U T n := by
  change 0≤a^omegaIn n U T/(n:ℝ)
  positivity

lemma intervalOmegaWeight_prime (a U T : ℝ) {p : ℕ} (hp : p.Prime) :
    intervalOmegaWeight a U T p = (if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ) := by
  classical
  by_cases h : U<(p:ℝ) ∧ (p:ℝ)≤T
  · simp [intervalOmegaWeight,omegaIn,Nat.primeFactorsList_prime hp,h]
  · simp only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,omegaIn,
      Nat.primeFactorsList_prime hp,List.filter_cons,List.filter_nil]
    simp [h,-Bool.decide_and]

lemma intervalOmegaWeight_norm {a : ℝ} (ha : 0≤a) (ha' : a≤3/2) (U T : ℝ)
    {p : ℕ} (hp : p.Prime) : ‖intervalOmegaWeight a U T p‖<1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (intervalOmegaWeight_nonneg ha U T p),
    intervalOmegaWeight_prime a U T hp]
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  apply (div_lt_one (by linarith : (0:ℝ)<p)).mpr
  split_ifs <;> linarith

/-- The exact finite Euler product; concentration bounds are proved separately. -/
lemma interval_omega_moment_product {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    (U T : ℝ) (N : ℕ) (Q : Finset ℕ) (hQ : ∀ n ∈ Q,0<n ∧ n≤N) :
    (∑ n ∈ Q,intervalOmegaWeight a U T n) ≤
      ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹ := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n∈Q) : n∈Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (Nat.le_of_mem_primeFactorsList hp).trans (hQ n hn).2⟩
  let e : {n // n∈Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let F : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q,intervalOmegaWeight a U T n) =
      ∑ n ∈ F,intervalOmegaWeight a U T n := by
    dsimp only [F]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q _).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=intervalOmegaWeight a U T) (fun {_} hp => intervalOmegaWeight_norm ha ha' U T hp) S
  calc
    _ = ∑ n ∈ F,intervalOmegaWeight a U T n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S,intervalOmegaWeight a U T n :=
      hs.1.of_norm.sum_le_tsum F (fun n _ => intervalOmegaWeight_nonneg ha U T n)
    _ = ∏ p ∈ S with p.Prime,(1-intervalOmegaWeight a U T p)⁻¹ := hs.2.tsum_eq
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [intervalOmegaWeight_prime a U T (Finset.mem_filter.mp hp).2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalEulerBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform quadratic control of the Euler factors for interval moments. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma interval_euler_log_factor {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    {p : ℕ} (hp : p.Prime) :
    Real.log ((1-a/(p:ℝ))⁻¹) ≤ a/(p:ℝ)+9/(p:ℝ)^2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hx0 : 0≤a/(p:ℝ) := div_nonneg ha hp0.le
  have hx : a/(p:ℝ)≤3/4 := (div_le_iff₀ hp0).mpr (by nlinarith)
  have hTaylor := Real.abs_log_sub_add_sum_range_le
    (show |a/(p:ℝ)|<1 by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    zero_add,pow_one,div_one,abs_of_nonneg hx0] at hTaylor
  have hquad : (a/(p:ℝ))^2/(1-a/(p:ℝ)) ≤ 9/(p:ℝ)^2 := by
    have hden : (1/4:ℝ)≤1-a/(p:ℝ) := by linarith
    calc
      _ ≤ (a/(p:ℝ))^2/(1/4) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
      _ = 4*a^2/(p:ℝ)^2 := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith
  have hh := (abs_le.mp hTaylor).1
  rw [Real.log_inv]
  linarith

lemma prime_reciprocal_squares_le (N : ℕ) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,1/(p:ℝ)^2) ≤ 1 := by
  have hs : (Finset.Icc 2 N).filter Nat.Prime ⊆ Finset.Ioo 1 (N+1) := by
    intro p hp
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Ioo.mpr ⟨by omega,by omega⟩
  calc
    _ ≤ ∑ p ∈ Finset.Ioo 1 (N+1),1/(p:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => by positivity)
    _ ≤ 1 := by
      have h := sum_Ioo_inv_sq_le (α:=ℝ) 1 (N+1)
      norm_num [one_div] at h ⊢
      exact h

lemma interval_euler_product_bound {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    (U T : ℝ) (N : ℕ) :
    (∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹) ≤
    Real.exp ((∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
      (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9) := by
  classical
  let P := (Finset.Icc 2 N).filter Nat.Prime
  let w := fun p : ℕ => if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1
  have hw (p : ℕ) : 0≤w p ∧ w p≤3/2 := by dsimp [w]; split_ifs <;> constructor <;> linarith
  have hfactor (p : ℕ) (hp : p∈P) : 0<(1-w p/(p:ℝ))⁻¹ := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    apply inv_pos.mpr
    have hh : w p/(p:ℝ)<1 := (div_lt_one (by linarith)).mpr (by have := hw p; linarith)
    linarith
  have hsum : (∑ p ∈ P,w p/(p:ℝ)) =
      (∑ p ∈ P,(p:ℝ)⁻¹)+(a-1)*(∑ p ∈ P.filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) := by
    have hf : (∑ p ∈ P.filter (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) =
        ∑ p ∈ P,if U<(p:ℝ) ∧ (p:ℝ)≤T then (p:ℝ)⁻¹ else 0 := Finset.sum_filter _ _
    rw [hf,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [w]
    split_ifs <;> ring
  have hlog : Real.log (∏ p ∈ P,(1-w p/(p:ℝ))⁻¹) ≤
      (∑ p ∈ P,(p:ℝ)⁻¹)+(a-1)*(∑ p ∈ P.filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9 := by
    rw [Real.log_prod (fun p hp => (hfactor p hp).ne')]
    calc
      _ ≤ ∑ p ∈ P,(w p/(p:ℝ)+9/(p:ℝ)^2) :=
        Finset.sum_le_sum (fun p hp => interval_euler_log_factor (hw p).1 (hw p).2
          (Finset.mem_filter.mp hp).2)
      _ = (∑ p ∈ P,w p/(p:ℝ))+9*(∑ p ∈ P,1/(p:ℝ)^2) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := by rw [hsum]; nlinarith [prime_reciprocal_squares_le N]
  exact (Real.log_le_iff_le_exp (Finset.prod_pos hfactor)).mp hlog

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensReciprocal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime sums from the second Mertens theorem. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeReciprocalLE_mertens : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLE x-Real.log (Real.log x)-Mertens.M| ≤ C/Real.log x := by
  refine ⟨Real.log 4+6+Mertens.E₁,?_,?_⟩
  · have hh := Mertens.E₁.nonneg
    have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    have hset : (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime=
        (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hp2,hpx⟩,hp⟩
        exact ⟨⟨by omega,hpx⟩,hp⟩
      · rintro ⟨⟨_,hpx⟩,hp⟩
        exact ⟨⟨hp.two_le,hpx⟩,hp⟩
    simpa only [primeReciprocalLE,primesUpTo,hset,one_div,Mertens.E₂p] using Mertens.E₂p.abs_le hx

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalPrimeMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reciprocal-prime mass in the intervals used for normality. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primesUpTo_mem {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p∈primesUpTo x ↔ p.Prime ∧ (p:ℝ)≤x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hpx⟩,hpp⟩
    exact ⟨hpp,(Nat.le_floor_iff hx).mp hpx⟩
  · rintro ⟨hpp,hpx⟩
    exact ⟨⟨hpp.two_le,(Nat.le_floor_iff hx).mpr hpx⟩,hpp⟩

lemma prime_interval_sum_eq (N : ℕ) {U T : ℝ} (hU : 2≤U) (hUT : U≤T) (hT : T≤N) :
    (∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
      (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) =
      primeReciprocalLE T-primeReciprocalLE U := by
  classical
  have hU0 : 0≤U := by linarith
  have hT0 : 0≤T := hU0.trans hUT
  have hsub : primesUpTo U ⊆ primesUpTo T := by
    intro p hp
    obtain ⟨hpp,hpU⟩ := (primesUpTo_mem hU0).mp hp
    exact (primesUpTo_mem hT0).mpr ⟨hpp,hpU.trans hUT⟩
  have hs : ((Finset.Icc 2 N).filter Nat.Prime).filter
      (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T) = primesUpTo T \ primesUpTo U := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_sdiff,
      primesUpTo_mem hU0,primesUpTo_mem hT0]
    constructor
    · rintro ⟨⟨⟨_,_⟩,hpp⟩,hpU,hpT⟩
      exact ⟨⟨hpp,hpT⟩,fun h => (not_le_of_gt hpU) h.2⟩
    · rintro ⟨⟨hpp,hpT⟩,hnot⟩
      have hpU : U<(p:ℝ) := lt_of_not_ge (fun h => hnot ⟨hpp,h⟩)
      have hpN : p≤N := by exact_mod_cast hpT.trans hT
      exact ⟨⟨⟨hpp.two_le,hpN⟩,hpp⟩,hpU,hpT⟩
  rw [hs,Finset.sum_sdiff_eq_sub hsub]
  rfl

lemma primeReciprocalLE_bounded_error : ∃ D : ℝ, 0<D ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLE x-B x|≤D := by
  obtain ⟨C,hC,hM⟩ := primeReciprocalLE_mertens
  refine ⟨2*C+|Mertens.M|,by positivity,?_⟩
  intro x hx
  have hlog : (1/2:ℝ)<Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    linarith [Real.log_two_gt_d9]
  have hquot : C/Real.log x≤2*C := by
    apply (div_le_iff₀ (by linarith : 0<Real.log x)).mpr
    nlinarith
  calc
    _ = |(primeReciprocalLE x-B x-Mertens.M)+Mertens.M| := by congr 1; ring
    _ ≤ |primeReciprocalLE x-B x-Mertens.M|+|Mertens.M| := abs_add_le _ _
    _ ≤ _ := add_le_add ((hM x hx).trans hquot) le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalMomentBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval prime-factor moment with its correct log-log exponent. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

 theorem interval_omega_moment_bound : ∃ C : ℝ, 0<C ∧
    ∀ a : ℝ, 0≤a → a≤3/2 → ∀ N : ℕ, 2≤N →
    ∀ U T : ℝ, 2≤U → U≤T → T≤N → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n≤N) →
    (∑ n ∈ Q,intervalOmegaWeight a U T n) ≤
      C*Real.log N*Real.exp ((a-1)*(B T-B U)) := by
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp (3*D+9),Real.exp_pos _,?_⟩
  intro a ha ha' N hN U T hU hUT hTN Q hQ
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hT : 2≤T := hU.trans hUT
  have hNerr := herr N hNR
  have hTerr := herr T hT
  have hUerr := herr U hU
  have hinterval : |(primeReciprocalLE T-primeReciprocalLE U)-(B T-B U)|≤2*D := by
    have h := abs_sub_le (primeReciprocalLE T-B T) 0 (primeReciprocalLE U-B U)
    simp only [sub_zero,zero_sub,abs_neg] at h
    have he : (primeReciprocalLE T-B T)-(primeReciprocalLE U-B U) =
        (primeReciprocalLE T-primeReciprocalLE U)-(B T-B U) := by ring
    rw [he] at h
    linarith
  have haabs : |a-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmul : (a-1)*((primeReciprocalLE T-primeReciprocalLE U)-(B T-B U))≤2*D := by
    calc
      _ ≤ |(a-1)*((primeReciprocalLE T-primeReciprocalLE U)-(B T-B U))| := le_abs_self _
      _ = |a-1| * |(primeReciprocalLE T-primeReciprocalLE U)-(B T-B U)| := abs_mul _ _
      _ ≤ 1*(2*D) := mul_le_mul haabs hinterval (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hmass : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)=primeReciprocalLE N := by
    simp only [primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have hexp : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
      (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9 ≤
      (3*D+9)+B N+(a-1)*(B T-B U) := by
    rw [hmass,prime_interval_sum_eq N hU hUT hTN]
    have hh := (abs_le.mp hNerr).2
    nlinarith
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  calc
    _ ≤ ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹ :=
      interval_omega_moment_product ha ha' U T N Q hQ
    _ ≤ Real.exp ((∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
        (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
          (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9) :=
      interval_euler_product_bound ha ha' U T N
    _ ≤ Real.exp ((3*D+9)+B N+(a-1)*(B T-B U)) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add,Real.exp_add]; simp only [B,Real.exp_log hlog]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalChernoff
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential deviation estimates for reciprocal cofactor mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma exp_small_tilt {t : ℝ} (ht : |t|≤1/4) :
    Real.exp t≤3/2 ∧ Real.exp t-1-t≤t^2 := by
  have hn : ‖t‖≤1 := by rw [Real.norm_eq_abs]; linarith
  have h := Real.norm_exp_sub_one_sub_id_le hn
  rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs] at h
  have ht' := abs_le.mp ht
  have hsq : t^2≤(1/4:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  have he := (abs_le.mp h).2
  constructor <;> nlinarith

/-- A single estimate handles the upper and lower tails by choosing the sign
of `t`. The mass uses every prime factor with multiplicity. -/
theorem interval_omega_chernoff : ∃ C : ℝ, 0<C ∧
    ∀ N : ℕ, 2≤N → ∀ U T : ℝ, 2≤U → U≤T → T≤N →
    ∀ t h : ℝ, |t|≤1/4 → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n≤N ∧ |t| *h≤t*((omegaIn n U T:ℝ)-(B T-B U))) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*
      Real.exp (t^2*(B T-B U)-|t| *h) := by
  obtain ⟨C,hC,hM⟩ := interval_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro N hN U T hU hUT hTN t h ht Q hQ
  let M := B T-B U
  let E := Real.exp (-|t| *h-t*M)
  have hM0 : 0≤M := sub_nonneg.mpr (Real.log_le_log
    (Real.log_pos (by linarith : (1:ℝ)<U))
    (Real.log_le_log (by linarith : (0:ℝ)<U) hUT))
  have htE := exp_small_tilt ht
  have hmass := hM (Real.exp t) (Real.exp_pos _).le htE.1 N hN U T hU hUT hTN Q
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hp (n : ℕ) (hn : n∈Q) : (n:ℝ)⁻¹ ≤ E*intervalOmegaWeight (Real.exp t) U T n := by
    have he : (Real.exp t)^omegaIn n U T = Real.exp (t*(omegaIn n U T:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hh : 1≤E*(Real.exp t)^omegaIn n U T := by
      rw [he,← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      dsimp [E,M]
      have := (hQ n hn).2.2
      linarith
    have hmul := mul_le_mul_of_nonneg_right hh (show 0≤(n:ℝ)⁻¹ by positivity)
    simpa only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,div_eq_mul_inv,
      mul_assoc,one_mul] using hmul
  calc
    _ ≤ E*(∑ n ∈ Q,intervalOmegaWeight (Real.exp t) U T n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hp
    _ ≤ E*(C*Real.log N*Real.exp ((Real.exp t-1)*M)) :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = C*Real.log N*Real.exp ((Real.exp t-1-t)*M-|t| *h) := by
      calc
        _ = C*Real.log N*(E*Real.exp ((Real.exp t-1)*M)) := by ring
        _ = _ := by
          dsimp [E]
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le
        (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))))
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right htE.2 hM0
      linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityTilt
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-root tilt giving the saving in the normality tail. -/
noncomputable section
namespace TotientAsymptotic

lemma normalityTilt_pos {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    0<normalityTilt A B := by
  have hB : 0<B := hA.trans_le hAB
  unfold normalityTilt
  exact div_pos (Real.sqrt_pos.mpr hA) (by positivity)

lemma normalityTilt_le {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    normalityTilt A B≤1/4 := by
  have hB : 0<B := hA.trans_le hAB
  unfold normalityTilt
  apply (div_le_iff₀ (by positivity : 0<4*Real.sqrt B)).mpr
  have hh := Real.sqrt_le_sqrt hAB
  nlinarith

lemma normalityTilt_exponent {A B M : ℝ} (hA : 0<A) (hAB : A≤B) (hM : M≤B) :
    (normalityTilt A B)^2*M-normalityTilt A B*(Real.sqrt (A*B)-4) ≤ 1-A/6 := by
  have hB : 0<B := hA.trans_le hAB
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsB : Real.sqrt B≠0 := (Real.sqrt_pos.mpr hB).ne'
  have h1 : normalityTilt A B * Real.sqrt (A*B) = A/4 := by
    rw [Real.sqrt_mul hA.le]
    unfold normalityTilt
    field_simp
    nlinarith
  have h2 : (normalityTilt A B)^2*B = A/16 := by
    unfold normalityTilt
    field_simp
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (sq_nonneg (normalityTilt A B))
  have ht := normalityTilt_le hA hAB
  rw [h2] at hm
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityIntervalTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal-mass saving for one interval in Ford's normality grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

 theorem normality_interval_mass : ∃ C : ℝ, 0<C ∧
    ∀ N : ℕ, 2≤N → ∀ U T A D : ℝ,
    2≤U → U≤T → T≤N → 0<A → A≤D → B T-B U≤D →
    ∀ Q : Finset ℕ, (∀ n ∈ Q,0<n ∧ n≤N ∧
      Real.sqrt (A*D)-4≤|(omegaIn n U T:ℝ)-(B T-B U)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hChernoff⟩ := interval_omega_chernoff
  refine ⟨2*C*Real.exp 1,by positivity,?_⟩
  intro N hN U T A D hU hUT hTN hA hAD hM Q hQ
  let δ := normalityTilt A D
  let h := Real.sqrt (A*D)-4
  let M := B T-B U
  let Qp := Q.filter (fun n => h≤(omegaIn n U T:ℝ)-M)
  let Qm := Q.filter (fun n => h≤-((omegaIn n U T:ℝ)-M))
  have hδ : 0<δ := normalityTilt_pos hA hAD
  have hδle : δ≤1/4 := normalityTilt_le hA hAD
  have hcover : Q⊆Qp∪Qm := by
    intro n hn
    have hh := (hQ n hn).2.2
    rw [le_abs] at hh
    rcases hh with hh|hh
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,by dsimp [h,M] <;> linarith⟩)
  have hplus : (∑ n ∈ Qp,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (δ^2*M-δ*h) := by
    have hc := hChernoff N hN U T hU hUT hTN δ h
      (by rw [abs_of_pos hδ]; exact hδle) Qp
    simp only [abs_of_pos hδ] at hc
    apply hc
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    refine ⟨(hQ n hn).1,(hQ n hn).2.1,?_⟩
    exact mul_le_mul_of_nonneg_left hh hδ.le
  have hminus : (∑ n ∈ Qm,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (δ^2*M-δ*h) := by
    have hc := hChernoff N hN U T hU hUT hTN (-δ) h
      (by rw [abs_neg,abs_of_pos hδ]; exact hδle) Qm
    simp only [neg_sq,abs_neg,abs_of_pos hδ] at hc
    apply hc
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    refine ⟨(hQ n hn).1,(hQ n hn).2.1,?_⟩
    have hm := mul_le_mul_of_nonneg_left hh hδ.le
    linarith
  have he : δ^2*M-δ*h ≤ 1-A/6 := normalityTilt_exponent hA hAD hM
  have hcoef : 0≤C*Real.log N := mul_nonneg hC.le
    (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega)))
  have hb : C*Real.log N*Real.exp (δ^2*M-δ*h) ≤
      C*Real.log N*(Real.exp 1*Real.exp (-A/6)) := by
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Qp∪Qm,(n:ℝ)⁻¹ := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun n _ _ => by positivity)
    _ ≤ (∑ n ∈ Qp,(n:ℝ)⁻¹)+(∑ n ∈ Qm,(n:ℝ)⁻¹) :=
      by
        have he := Finset.sum_union_inter (s₁:=Qp) (s₂:=Qm) (f:=fun n : ℕ => (n:ℝ)⁻¹)
        have hn : 0≤∑ n ∈ Qp∩Qm,(n:ℝ)⁻¹ := Finset.sum_nonneg (fun n _ => by positivity)
        linarith
    _ ≤ 2*(C*Real.log N*Real.exp (δ^2*M-δ*h)) := by linarith
    _ ≤ 2*(C*Real.log N*(Real.exp 1*Real.exp (-A/6))) := by linarith
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridCell
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the interval deviations over the finite normality grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normalityGridPoint_two_le (j : ℕ) : (2:ℝ) ≤ normalityGridPoint j := by
  have h1 := Real.one_le_exp (Nat.cast_nonneg j : (0:ℝ) ≤ j)
  have h2 := Real.add_one_le_exp (Real.exp (j:ℝ))
  dsimp [normalityGridPoint]
  linarith

lemma normality_grid_cell_mass : ∃ C : ℝ, 0<C ∧ ∀ N M : ℕ,
    2 ≤ N → normalityGridPoint M ≤ N → ∀ A : ℝ, 0<A → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n ≤ N) → ∀ ij : ℕ×ℕ,
    (∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hbound⟩ := normality_interval_mass
  refine ⟨C,hC,?_⟩
  intro N M hN hMN A hA Q hQ ij
  by_cases he : (normalityGridCell A M Q ij).Nonempty
  · obtain ⟨m,hm⟩ := he
    obtain ⟨_,hi,hij,hj,hD,_⟩ := Finset.mem_filter.mp hm
    apply hbound N hN (normalityGridPoint ij.1) (normalityGridPoint ij.2) A ((ij.2:ℝ)-1)
      (normalityGridPoint_two_le _) (normalityGridPoint_mono hij).le
      ((normalityGridPoint_mono.monotone hj).trans hMN) hA hD
    · rw [normalityGridPoint_B,normalityGridPoint_B]
      have hiR : (1:ℝ) ≤ ij.1 := by exact_mod_cast hi
      linarith
    · intro n hn
      obtain ⟨hn,_,_,_,_,hh⟩ := Finset.mem_filter.mp hn
      exact ⟨(hQ n hn).1,(hQ n hn).2,by simpa only [normalityGridPoint_B] using hh⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC.le (Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ N by omega)))) (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite union of the normality grid cells. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace TotientAsymptotic

lemma normality_grid_constant_sum (M : ℕ) (W : ℝ) :
    (∑ _ij ∈ normalityGridIndices M,W) = (((M+1:ℕ):ℝ))^2*W := by
  have hc : (normalityGridIndices M).card = (M+1)*(M+1) := by
    exact (Finset.card_product (Finset.range (M+1)) (Finset.range (M+1))).trans
      (by rw [Finset.card_range])
  rw [Finset.sum_const,hc]
  simp only [nsmul_eq_mul,Nat.cast_mul,pow_two]

lemma normality_grid_cover (A : ℝ) (M : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,∃ i j : ℕ,1 ≤ i ∧ i < j ∧ j ≤ M ∧ A ≤ (j:ℝ)-1 ∧
      Real.sqrt (A*((j:ℝ)-1))-4 ≤
      |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)|) :
    Q ⊆ (normalityGridIndices M).biUnion (normalityGridCell A M Q) := by
  classical
  intro n hn
  obtain ⟨i,j,hi,hij,hj,hD,hh⟩ := hQ n hn
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega)⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨hn,hi,hij,hj,hD,hh⟩

lemma reciprocal_sum_biUnion_le {α : Type*} (I : Finset α) (S : α → Finset ℕ) :
    (∑ n ∈ I.biUnion S,(n:ℝ)⁻¹) ≤ ∑ i ∈ I,∑ n ∈ S i,(n:ℝ)⁻¹ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁:=S a) (s₂:=I.biUnion S) (f:=fun n : ℕ => (n:ℝ)⁻¹)
    have hn : 0 ≤ ∑ n ∈ S a ∩ I.biUnion S,(n:ℝ)⁻¹ :=
      Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    linarith

lemma normality_grid_sum_bound (A : ℝ) (M : ℕ) (Q : Finset ℕ) (W : ℝ)
    (hcover : Q ⊆ (normalityGridIndices M).biUnion (normalityGridCell A M Q))
    (hF : ∀ ij, (∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹) ≤ W) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ (((M+1:ℕ):ℝ))^2*W := by
  classical
  calc
    _ ≤ ∑ n ∈ (normalityGridIndices M).biUnion (normalityGridCell A M Q),(n:ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ ij ∈ normalityGridIndices M,∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹ :=
      reciprocal_sum_biUnion_le (normalityGridIndices M) (normalityGridCell A M Q)
    _ ≤ ∑ _ij ∈ normalityGridIndices M,W := Finset.sum_le_sum (fun ij _ => hF ij)
    _ = _ := normality_grid_constant_sum M W

theorem normality_grid_mass : ∃ C : ℝ, 0<C ∧ ∀ N M : ℕ,
    2 ≤ N → normalityGridPoint M ≤ N → ∀ A : ℝ, 0<A → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n ≤ N ∧ ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ M ∧ A ≤ (j:ℝ)-1 ∧
      Real.sqrt (A*((j:ℝ)-1))-4 ≤
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*(((M+1:ℕ):ℝ))^2*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hbound⟩ := normality_grid_cell_mass
  refine ⟨C,hC,?_⟩
  intro N M hN hMN A hA Q hQ
  have hcover := normality_grid_cover A M Q (fun n hn => (hQ n hn).2.2)
  have hF := hbound N M hN hMN A hA Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hh := normality_grid_sum_bound A M Q (C*Real.log N*Real.exp (-A/6)) hcover hF
  calc
    _ ≤ (((M+1:ℕ):ℝ))^2*(C*Real.log N*Real.exp (-A/6)) := hh
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridReduction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reduction of a real interval deviation to a double-logarithmic grid interval. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_grid_reduction (n : ℕ) {S U T x : ℝ}
    (hS : 1 < S) (hBS : 4 ≤ B S) (hSU : S ≤ U) (hUT : U < T) (hTx : T ≤ x)
    (hbad : Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|) :
    ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ ⌊B x⌋₊+1 ∧
      B S-2 ≤ (j:ℝ)-1 ∧
      Real.sqrt ((B S-2)*((j:ℝ)-1))-4  ≤ 
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)| := by
  have hU : 1 < U := hS.trans_le hSU
  have hT : 1 < T := hU.trans hUT
  have hx : 1 < x := hT.trans_le hTx
  have hBU : B S ≤ B U := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (by linarith) hSU)
  have hBT : B U ≤ B T := Real.log_le_log (Real.log_pos hU)
    (Real.log_le_log (by linarith) hUT.le)
  have hBT4 : 4 ≤ B T := hBS.trans (hBU.trans hBT)
  have hBx : B T ≤ B x := Real.log_le_log (Real.log_pos hT)
    (Real.log_le_log (by linarith) hTx)
  let a := ⌊B U⌋₊
  let b := ⌊B T⌋₊
  have ha0 : 0 ≤ B U := by linarith
  have hb0 : 0 ≤ B T := by linarith
  have haL : (a:ℝ) ≤ B U := Nat.floor_le ha0
  have haR : B U < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbL : (b:ℝ) ≤ B T := Nat.floor_le hb0
  have hbR : B T < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have ha4 : 4 ≤ a := (Nat.le_floor_iff ha0).mpr (by norm_num <;> linarith)
  have hab : a ≤ b := Nat.floor_mono hBT
  have hbx : b ≤ ⌊B x⌋₊ := Nat.floor_mono hBx
  have hu := normalityGridPoint_bracket hU ha0
  have ht := normalityGridPoint_bracket hT hb0
  have hroot : 4 ≤ Real.sqrt (B S*B T) := by
    have hnon := Real.sqrt_nonneg (B S*B T)
    have he := Real.sq_sqrt (show 0 ≤ B S*B T by positivity)
    nlinarith
  have hroot_compare (j : ℕ) (hD0 : 0 ≤ (j:ℝ)-1) (hD : (j:ℝ)-1 ≤ B T) :
      Real.sqrt ((B S-2)*((j:ℝ)-1))  ≤  Real.sqrt (B S*B T) := by
    apply Real.sqrt_le_sqrt
    have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ B S-2 by linarith)
    nlinarith
  rcases le_abs.mp hbad with hhigh|hlow
  · refine ⟨a,b+1,by omega,by omega,by omega,?_,?_⟩
    · push_cast
      linarith
    · have hc := omegaIn_mono n hu.1 ht.2.le
      have hcR : (omegaIn n U T:ℝ) ≤ omegaIn n (normalityGridPoint a) (normalityGridPoint (b+1)) := by
        exact_mod_cast hc
      have hr := hroot_compare (b+1) (by push_cast; have hb : (0:ℝ) ≤ b := Nat.cast_nonneg _; linarith) (by push_cast <;> linarith)
      apply le_trans _ (le_abs_self _)
      push_cast at hr ⊢
      nlinarith
  · have hsep : a+1 < b := by
      by_contra hn
      have hn' : (b:ℝ) ≤ (a:ℝ)+1 := by exact_mod_cast (by omega : b ≤ a+1)
      have hΩ : (0:ℝ) ≤ omegaIn n U T := Nat.cast_nonneg _
      nlinarith
    refine ⟨a+1,b,by omega,hsep,by omega,?_,?_⟩
    · linarith
    · have hc := omegaIn_mono n (U₁:=normalityGridPoint (a+1)) (U₂:=U)
        (T₁:=normalityGridPoint b) (T₂:=T) hu.2.le ht.1
      have hcR : (omegaIn n (normalityGridPoint (a+1)) (normalityGridPoint b):ℝ) ≤ omegaIn n U T := by
        exact_mod_cast hc
      have hb1 : (1:ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
      have hr := hroot_compare b (by linarith) (by linarith)
      apply le_trans _ (neg_le_abs _)
      push_cast
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AbnormalIntervalMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal cofactor mass for all failed interval normality conditions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem abnormal_interval_mass : ∃ C : ℝ, 0 < C ∧ ∀ S x : ℝ,
    1 < S → 4 ≤ B S → Real.exp 1 ≤ x → 1 ≤ B x → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ (n:ℝ) ≤ x ∧ ∃ U T : ℝ, S ≤ U ∧ U < T ∧ T ≤ x ∧
      Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹)  ≤  C*(B x)^2*Real.log x*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hgrid⟩ := normality_grid_mass
  refine ⟨9*C*(Real.exp 1+1)*Real.exp (1/3),by positivity,?_⟩
  intro S x hS hBS hx hBx Q hQ
  let M := ⌊B x⌋₊+1
  let N := normalityGridEnvelope x
  have hen := normalityGridEnvelope_bounds hx
  have hB0 : 0 ≤ B x := by linarith
  have hA : 0 < B S-2 := by linarith
  have hQ' : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ ∃ i j : ℕ,
      1 ≤ i ∧ i < j ∧ j ≤ M ∧ B S-2 ≤ (j:ℝ)-1 ∧
      Real.sqrt ((B S-2)*((j:ℝ)-1))-4 ≤ 
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)| := by
    intro n hn
    obtain ⟨hn0,hnx,U,T,hSU,hUT,hTx,hbad⟩ := hQ n hn
    have hnN : n ≤ N := by exact_mod_cast hnx.trans hen.1
    exact ⟨hn0,hnN,normality_grid_reduction n hS hBS hSU hUT hTx hbad⟩
  have hg := hgrid N M hen.2.1 hen.2.2.1 (B S-2) hA Q hQ'
  have hM : ((M+1:ℕ):ℝ) ≤ 3*B x := by
    dsimp [M]
    push_cast
    have hh := Nat.floor_le hB0
    linarith
  have hsq : (((M+1:ℕ):ℝ))^2 ≤ (3*B x)^2 := pow_le_pow_left₀ (by positivity) hM 2
  have he : Real.exp (-(B S-2)/6)=Real.exp (1/3)*((Real.log S)^(-1/6:ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hS),← Real.exp_add]
    unfold B
    congr 1
    ring
  have hlogx : 0 ≤ Real.log x := by
    have h0 := (Real.exp_pos 1).trans_le hx
    have hh := (Real.le_log_iff_exp_le h0).mpr hx
    linarith
  calc
    _  ≤  C*(((M+1:ℕ):ℝ))^2*Real.log N*Real.exp (-(B S-2)/6) := by
      exact_mod_cast hg
    _  ≤  C*(3*B x)^2*((Real.exp 1+1)*Real.log x)*Real.exp (-(B S-2)/6) := by
      gcongr
      exact hen.2.2.2
    _ = _ := by rw [he]; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallFactorMoment
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A three-halves moment counting only prime factors at most S. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma small_factor_moment_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ S : ℝ, 2 ≤ S → ∀ Q : Finset ℕ, (∀ n ∈ Q,0 < n ∧ n ≤ N) →
    (∑ n ∈ Q,intervalOmegaWeight (3/2) 1 S n) ≤
      C*Real.log N*Real.exp (B S/2) := by
  classical
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((3/2:ℝ)*D+9),Real.exp_pos _,?_⟩
  intro N hN S hS Q hQ
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hsub : P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S) ⊆ primesUpTo S := by
    intro p hp
    obtain ⟨hp,hpS⟩ := Finset.mem_filter.mp hp
    exact (primesUpTo_mem (by linarith)).mpr ⟨(Finset.mem_filter.mp hp).2,hpS.2⟩
  have hs : (∑ p ∈ P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S),(p:ℝ)⁻¹) ≤
      primeReciprocalLE S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hn : (∑ p ∈ P,(p:ℝ)⁻¹) = primeReciprocalLE N := by
    simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have hnerr := (abs_le.mp (herr N (by exact_mod_cast hN))).2
  have hserr := (abs_le.mp (herr S hS)).2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ ∏ p ∈ P,(1-(if (1:ℝ) < p ∧ (p:ℝ) ≤ S then (3/2:ℝ) else 1)/(p:ℝ))⁻¹ :=
      interval_omega_moment_product (by norm_num) (by norm_num) 1 S N Q hQ
    _ ≤ Real.exp ((∑ p ∈ P,(p:ℝ)⁻¹)+
        ((3/2:ℝ)-1)*(∑ p ∈ P.filter (fun p : ℕ => (1:ℝ) < p ∧ (p:ℝ) ≤ S),(p:ℝ)⁻¹)+9) :=
      interval_euler_product_bound (by norm_num) (by norm_num) 1 S N
    _ ≤ Real.exp (((3/2:ℝ)*D+9)+B N+B S/2) := by
      apply Real.exp_le_exp.mpr
      rw [hn]
      linarith
    _ = _ := by
      rw [Real.exp_add,Real.exp_add]
      simp only [B,Real.exp_log hlog]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallFactorTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal mass of cofactors with too many small prime factors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma log_three_halves_lower : (1/3:ℝ) ≤ Real.log (3/2:ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 3/2)
  norm_num at h ⊢
  exact h

lemma small_factor_tail_weight {S : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 2*B S-1 < (omegaIn n 1 S:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*intervalOmegaWeight (3/2) 1 S n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(3/2:ℝ)^(omegaIn n 1 S) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3/2),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

 theorem small_factor_tail_mass : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ S : ℝ, 2 ≤ S → 0 ≤ B S → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 2*B S-1 < (omegaIn n 1 S:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*Real.log N*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := small_factor_moment_bound
  refine ⟨(3/2:ℝ)*C,by positivity,?_⟩
  intro N hN S hS hBS Q hQ
  have hm := hbound N hN S hS Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hexp : Real.exp ((1-2*B S)*Real.log (3/2:ℝ)+B S/2) ≤
      (3/2:ℝ)*(Real.log S)^(-1/6:ℝ) := by
    rw [Real.rpow_def_of_pos hlog,show (3/2:ℝ)=Real.exp (Real.log (3/2:ℝ)) from
      (Real.exp_log (by norm_num)).symm,← Real.exp_add]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    unfold B at *
    nlinarith [log_three_halves_lower]
  calc
    _ ≤ ∑ n ∈ Q,Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*intervalOmegaWeight (3/2) 1 S n :=
      Finset.sum_le_sum (fun n hn => small_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
    _ = Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(∑ n ∈ Q,intervalOmegaWeight (3/2) 1 S n) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp ((1-2*B S)*Real.log (3/2:ℝ))*(C*Real.log N*Real.exp (B S/2)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = C*Real.log N*Real.exp ((1-2*B S)*Real.log (3/2:ℝ)+B S/2) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.log N*((3/2:ℝ)*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hC.le hNlog)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AbnormalCofactorMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both failures of prime normality have small reciprocal cofactor mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

 theorem abnormal_cofactor_mass : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → 4 ≤ B S →
    ∀ N : ℕ, Real.exp 1 ≤ N → 1 ≤ B N → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ AbnormalCofactor S N n) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hsmall⟩ := small_factor_tail_mass
  obtain ⟨D,hD,hinterval⟩ := abnormal_interval_mass
  refine ⟨C+D,by positivity,?_⟩
  intro S hS hBS N hN hBN Q hQ
  let Q₁ := Q.filter (fun n => 2*B S-1 < (omegaIn n 1 S:ℝ))
  let Q₂ := Q.filter (fun n => ¬2*B S-1 < (omegaIn n 1 S:ℝ))
  have hN2 : 2 ≤ N := by
    have he := Real.add_one_le_exp (1:ℝ)
    have hh : (2:ℝ) ≤ N := by linarith
    exact_mod_cast hh
  have hs := hsmall N hN2 S hS.le (by linarith) Q₁ (by
    intro n hn
    obtain ⟨hn,hb⟩ := Finset.mem_filter.mp hn
    exact ⟨(hQ n hn).1,(hQ n hn).2.1,hb⟩)
  have hi := hinterval S N (by linarith) hBS hN hBN Q₂ (by
    intro n hn
    obtain ⟨hn,hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0,hnN,hbad⟩ := hQ n hn
    refine ⟨hn0,by exact_mod_cast hnN,?_⟩
    exact hbad.resolve_left hb)
  have heq : (∑ n ∈ Q,(n:ℝ)⁻¹) = (∑ n ∈ Q₁,(n:ℝ)⁻¹)+(∑ n ∈ Q₂,(n:ℝ)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not Q (fun n => 2*B S-1 < (omegaIn n 1 S:ℝ)) _).symm
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hscale : 1 ≤ (B N)^2 := by nlinarith
  have hs' : C*Real.log N*(Real.log S)^(-1/6:ℝ) ≤
      C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hscale
      (show 0 ≤ C*Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
    nlinarith
  rw [heq]
  calc
    _ ≤ C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ)+
        D*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := add_le_add (hs.trans hs') hi
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCofactorMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Rankin moment for the smooth cofactor discarded in extraction. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma powerReciprocal_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ powerReciprocal σ n := by
  change 0 ≤ (n : ℝ)^σ/(n : ℝ)
  positivity

lemma powerReciprocal_prime_norm {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime) :
    ‖powerReciprocal σ p‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)]
  change (p : ℝ)^σ/(p : ℝ) < 1
  rw [div_lt_one (zero_lt_one.trans hp1)]
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hp1 hσ

lemma powerReciprocal_euler_factor {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime)
    (hpow : (p : ℝ)^σ ≤ 3/2) :
    (1-powerReciprocal σ p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  have hnorm := powerReciprocal_prime_norm hσ hp
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hnorm
  have hb : powerReciprocal σ p ≤ omegaReciprocal p := by
    rw [omegaReciprocal_prime hp]
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hω := omegaReciprocal_prime_norm hp
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p)] at hω
  have hh := one_div_le_one_div_of_le (by linarith : 0 < 1-omegaReciprocal p)
    (sub_le_sub_left hb 1)
  rw [one_div,one_div] at hh
  exact hh.trans (omega_euler_factor_le hp)

lemma smooth_power_reciprocal_mass {σ : ℝ} (hσ : σ < 1) (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N)
    (hpow : ∀ p : ℕ, p.Prime → p ≤ N → (p : ℝ)^σ ≤ 3/2) :
    (∑ n ∈ Q, powerReciprocal σ n) ≤ (primeEulerProduct N)^3 := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (primeFactor_le_largest hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, powerReciprocal σ n) = ∑ n ∈ T, powerReciprocal σ n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => powerReciprocal σ n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerReciprocal σ) (fun {_} hp => powerReciprocal_prime_norm hσ hp) S
  calc
    _ = ∑ n ∈ T, powerReciprocal σ n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, powerReciprocal σ n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => powerReciprocal_nonneg σ n)
    _ = ∏ p ∈ S with p.Prime, (1-powerReciprocal σ p)⁻¹ := hs.2.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, ((p : ℝ)/(p-1))^3 := by
      apply Finset.prod_le_prod
      · intro p hp
        have hh := powerReciprocal_prime_norm hσ (Finset.mem_filter.mp hp).2
        rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hh
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact powerReciprocal_euler_factor hσ (Finset.mem_filter.mp hp).2
          (hpow p (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
    _ = _ := by rw [Finset.prod_pow]; rfl

lemma totient_ratio_le_eulerProduct_of_smooth {n N : ℕ} (hn : 0 < n)
    (hs : largestPrimeFactor n ≤ N) : (n : ℝ)/n.totient ≤ primeEulerProduct N := by
  rw [totient_ratio_product hn]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.two_le,
      (primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn.ne' hprime).mpr
        (Nat.dvd_of_mem_primeFactors hp))).trans hs⟩,hprime⟩
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · intro p hp _
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p-1)).mpr
    linarith

lemma quarter_log_power {N p : ℕ} (hN : 2 ≤ N) (hp : p.Prime) (hpN : p ≤ N) :
    (p : ℝ)^(1/(4*Real.log N)) ≤ 3/2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl := Real.log_le_log hp0 (show (p : ℝ) ≤ N by exact_mod_cast hpN)
  rw [Real.rpow_def_of_pos hp0]
  have hexp : Real.exp (1/4 : ℝ) ≤ 3/2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) < 1)
    norm_num at hh
    linarith
  apply (Real.exp_le_exp.mpr ?_).trans hexp
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.log N)).mpr
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma quarter_log_exponent_lt_one {N : ℕ} (hN : 2 ≤ N) : 1/(4*Real.log N) < (1 : ℝ) := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hlog2 := Real.log_two_gt_d9
  apply (div_lt_one (by nlinarith : (0 : ℝ)<4*Real.log N)).mpr
  nlinarith

/-- A coarse fourth power of the Mertens product suffices for the tail;
no asymptotic estimate for smooth integers is assumed. -/
theorem smooth_cofactor_power_mass {N : ℕ} (hN : 2 ≤ N) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)^(1/(4*Real.log N))/(n.totient : ℝ)) ≤ (primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hE : 0 ≤ primeEulerProduct N := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  calc
    _ ≤ primeEulerProduct N*∑ n ∈ Q, powerReciprocal σ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hb := mul_le_mul_of_nonneg_right
        (totient_ratio_le_eulerProduct_of_smooth (hQ n hn).1 (hQ n hn).2)
        (powerReciprocal_nonneg σ n)
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [powerReciprocal,σ]
      field_simp
    _ ≤ primeEulerProduct N*(primeEulerProduct N)^3 :=
      mul_le_mul_of_nonneg_left
        (smooth_power_reciprocal_mass (quarter_log_exponent_lt_one hN) N Q hQ
          (fun p hp hpN => quarter_log_power hN hp hpN)) hE
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensEuler
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler product controlled by a convergent real power series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace TotientAsymptotic

lemma negative_power_sum_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ 1+1/(s-1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-s)) 1
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (by simpa using hx)) hxy (by linarith))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (zero_lt_one.trans (by simpa using hx)).le _)
  simp only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ)<1)] at htail
  have he : (∑' n : ℕ, (n : ℝ)^(-s))=1+∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s) := by
    rw [← hsum.sum_add_tsum_nat_add 2]
    norm_num [Finset.sum_range_succ,show s≠0 by linarith]
    congr 1
    funext n
    congr 1
    ring
  rw [he]
  have htail' : (∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s)) ≤ 1/(s-1) := by
    have hi : -(1 : ℝ)^(-s+1)/(-s+1)=1/(s-1) := by
      rw [Real.one_rpow,show -s+1= -(s-1) by ring]
      simp only [div_neg,neg_div,neg_neg]
    exact hi ▸ htail
  linarith

lemma finite_power_euler_product_le {s : ℝ} (hs : 1 < s) (S : Finset ℕ) :
    (∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹) ≤ 1+1/(s-1) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖negativePower s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)
      (show -s<0 by linarith)
    simpa only [Real.rpow_zero] using h
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePower s) hp S
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb := hsum.tsum_subtype_le (fun n : ℕ => (n : ℝ)^(-s))
    (Nat.factoredNumbers S) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heq : (∑' n : Nat.factoredNumbers S, negativePower s n)=
      ∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹ := he.2.tsum_eq
  exact heq.symm.trans_le (hb.trans (negative_power_sum_le hs))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensLogMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite summation-by-parts bound sufficient for the Mertens product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma weighted_sum_le_harmonic (a : ℕ → ℝ) (C : ℝ)
    (ha0 : a 0=0)
    (hA : ∀ n : ℕ, (∑ i ∈ Finset.range (n+1), a i) ≤ C*(n+1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), a i/(i : ℝ)) ≤
      (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ) := by
  induction n with
  | zero => simp [ha0]
  | succ n ih =>
    have hn : (0 : ℝ)<n+1 := by positivity
    have hn2 : (0 : ℝ)<n+2 := by positivity
    let A := ∑ i ∈ Finset.range (n+2), a i
    have hA' : A ≤ C*(n+2) := by
      convert hA (n+1) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    have hstep : A/(n+1) ≤ A/(n+2)+C/(n+1) := by
      apply (div_le_iff₀ hn).mpr
      have hdiv : A/(n+2) ≤ C := (div_le_iff₀ hn2).mpr hA'
      have he : A/(n+2)*(n+2)=A := div_mul_cancel₀ A hn2.ne'
      rw [add_mul,div_mul_cancel₀ _ hn.ne']
      nlinarith
    have hrec : A=(∑ i ∈ Finset.range (n+1), a i)+a (n+1) := by
      exact Finset.sum_range_succ a (n+1)
    calc
      _ = (∑ i ∈ Finset.range (n+1), a i/(i : ℝ))+a (n+1)/(n+1) := by
        rw [Finset.sum_range_succ]
        push_cast
        rfl
      _ ≤ (∑ i ∈ Finset.range (n+1), a i)/(n+1)+C*(harmonic n : ℝ)+
          a (n+1)/(n+1) := add_le_add ih le_rfl
      _ = A/(n+1)+C*(harmonic n : ℝ) := by
        rw [hrec,add_div]
        ring
      _ ≤ A/(n+2)+C/(n+1)+C*(harmonic n : ℝ) := add_le_add hstep le_rfl
      _ = _ := by
        rw [harmonic_succ]
        push_cast
        dsimp [A]
        ring

/-- Only a coarse logarithmic bound is needed; no Mertens theorem is assumed. -/
lemma prime_log_mass_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)) ≤
      Real.log 4*(2+Real.log N) := by
  classical
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have he (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i)=Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,← Nat.range_succ_eq_Icc_zero,
      Finset.sum_filter]

  have hA (n : ℕ) : (∑ i ∈ Finset.range (n+1), a i) ≤ Real.log 4*(n+1) := by
    rw [he]
    have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hb := weighted_sum_le_harmonic a (Real.log 4) (by simp [a]) hA N
  have hsum : (∑ i ∈ Finset.range (N+1), a i/(i : ℝ))=
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ) := by
    rw [Nat.range_succ_eq_Icc_zero,Finset.sum_filter]
    simp only [a,ite_div,zero_div]
    symm
    apply Finset.sum_subset (fun p hp => by
      have hh := Finset.mem_Icc.mp hp
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩)
    · intro p hp hnot
      have hp2 : p<2 := by
        have hh := Finset.mem_Icc.mp hp
        simp only [Finset.mem_Icc,not_and_or,not_le] at hnot
        omega
      have hprime : ¬p.Prime := fun hh => (not_le_of_gt hp2) hh.two_le
      simp [hprime]
  rw [hsum] at hb
  have ht := (div_le_iff₀ (show (0 : ℝ)<N+1 by positivity)).mpr (hA N)
  have hh := harmonic_le_one_add_log N
  have hc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh hc
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensFactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the ordinary and convergent prime Euler factors. -/
noncomputable section
namespace TotientAsymptotic

lemma mertens_factor_le {u : ℝ} (hu : 0<u) {p : ℕ} (hp : p.Prime) :
    (p : ℝ)/(p-1) ≤ Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ)<p := by linarith
  have hd : (0 : ℝ)<p-1 := by linarith
  have hv : 0≤u*Real.log p := mul_nonneg hu.le (Real.log_nonneg (by linarith))
  have hpow : (p : ℝ)^(-(1+u))=(p : ℝ)⁻¹*Real.exp (-(u*Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]
    have he : Real.log (p : ℝ)*(-(1+u))= -Real.log p+ -(u*Real.log p) := by ring
    rw [he,Real.exp_add,Real.exp_neg,Real.exp_log hp0]
  have hpowlt : (p : ℝ)^(-(1+u))<1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by linarith)
      (show -(1+u)<0 by linarith)
    simpa using h
  have hB : 0<1-(p : ℝ)^(-(1+u)) := by linarith
  have hr : (1 : ℝ)/(p-1)≤2/p := by
    apply (div_le_div_iff₀ hd hp0).mpr
    nlinarith
  have he : (p : ℝ)/(p-1)*(1-(p : ℝ)^(-(1+u))) ≤ Real.exp (2*u*Real.log p/p) := by
    calc
      _ = 1+(1-Real.exp (-(u*Real.log p)))/(p-1) := by
        rw [hpow]
        field_simp
        ring
      _ ≤ 1+(u*Real.log p)/(p-1) := by
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_right _ hd.le
        linarith [Real.one_sub_le_exp_neg (u*Real.log p)]
      _ ≤ 1+2*u*Real.log p/p := by
        have hh := mul_le_mul_of_nonneg_left hr hv
        first | (convert add_le_add_left hh 1 using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((add_le_add_left hh 1).trans (le_of_eq (by ring)))
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2*u*Real.log p/p)
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hB).mpr he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete Mertens upper bound used by the totient asymptotic. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_rankin {u : ℝ} (hu : 0<u) (N : ℕ) :
    primeEulerProduct N ≤
      Real.exp (2*u*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        Real.log p/(p : ℝ)))*(1+1/u) := by
  let S := (Finset.Icc 2 N).filter Nat.Prime
  have he : (∏ p ∈ S, Real.exp (2*u*Real.log p/p))=
      Real.exp (2*u*(∑ p ∈ S, Real.log p/p)) := by
    rw [← Real.exp_sum,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  calc
    primeEulerProduct N ≤ ∏ p ∈ S,
        Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact mertens_factor_le hu (Finset.mem_filter.mp hp).2
    _ = Real.exp (2*u*(∑ p ∈ S, Real.log p/p))*
        ∏ p ∈ S, (1-(p : ℝ)^(-(1+u)))⁻¹ := by
      rw [Finset.prod_mul_distrib,he]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hh := finite_power_euler_product_le (show 1<1+u by linarith) (Finset.Icc 2 N)
      simpa only [add_sub_cancel_left] using hh

/-- Mertens' full asymptotic is unnecessary here: Chebyshev, finite Euler
products and the integral test prove exactly the required upper bound. -/
theorem mertensProductInput : MertensProductInput := by
  refine ⟨3*Real.exp (10*Real.log 4),by positivity,?_⟩
  intro N hN
  have hlog : (1/2 : ℝ)<Real.log N := by
    have hn : (2 : ℝ)≤N := by exact_mod_cast hN
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<2) hn
    linarith [Real.log_two_gt_d9]
  have hc : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hu : 0<1/Real.log N := by positivity
  have hb := primeEulerProduct_rankin hu N
  have hm := mul_le_mul_of_nonneg_left (prime_log_mass_le N hN)
    (show 0≤2*(1/Real.log N) by positivity)
  have hexp : 2*(1/Real.log N)*(∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      Real.log p/(p : ℝ)) ≤ 10*Real.log 4 := by
    have hi : 1/Real.log N≤2 := by
      apply (div_le_iff₀ (by linarith : 0<Real.log N)).mpr
      linarith
    have he : 2*(1/Real.log N)*(Real.log 4*(2+Real.log N))=
        4*(1/Real.log N)*Real.log 4+2*Real.log 4 := by
      field_simp
      ring
    rw [he] at hm
    nlinarith
  have hlast : 1+1/(1/Real.log N) ≤ 3*Real.log N := by
    simp only [one_div_one_div]
    linarith
  calc
    primeEulerProduct N ≤ Real.exp (2*(1/Real.log N)*
        (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p/(p : ℝ)))*
        (1+1/(1/Real.log N)) := hb
    _ ≤ Real.exp (10*Real.log 4)*(3*Real.log N) :=
      mul_le_mul (Real.exp_le_exp.mpr hexp) hlast (by positivity) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorSieveCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic endpoint for the cofactor prime-pair sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma floor_log_endpoint {L z : ℝ} (hL : 1 ≤ L) (hz : Real.exp (2*L) ≤ z) :
    2 ≤ ⌊z⌋₊ ∧ L ≤ Real.log (⌊z⌋₊:ℝ) := by
  have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hz0 : 0 ≤ z := (Real.exp_pos _).le.trans hz
  have htwo : 2*Real.exp L ≤ z := by
    have heq : Real.exp (2*L) = (Real.exp L)^2 := by
      rw [show 2*L=L+L by ring,Real.exp_add,pow_two]
    rw [heq] at hz
    nlinarith
  have hf := Nat.lt_floor_add_one z
  have heFloor : Real.exp L ≤ (⌊z⌋₊:ℝ) := by linarith
  have hN : 2 ≤ ⌊z⌋₊ := by exact_mod_cast he.trans heFloor
  refine ⟨hN,?_⟩
  exact (Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega))).mpr heFloor

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullOmegaMoment
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp three-halves moment needed for the small-prime-factor excess. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_all_factors {n N : ℕ} (hn : 0<n) (hnN : n≤N) :
    omegaIn n 1 N = n.primeFactorsList.length := by
  unfold omegaIn
  rw [List.filter_eq_self.mpr]
  intro p hp
  simp only [decide_eq_true_eq]
  constructor
  · exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).one_lt
  · exact_mod_cast (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hp)).trans hnN

/-- The exponent three used in coarse extraction bounds is sharpened to three
halves here, as required by the normality exception estimate. -/
theorem full_omega_moment_bound : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2≤N →
    ∀ Q : Finset ℕ, (∀ n ∈ Q,0<n ∧ n≤N) →
      (∑ n ∈ Q,omegaReciprocal n) ≤ C*(Real.log N)^(3/2:ℝ) := by
  classical
  obtain ⟨D,hD,hDerr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((3/2:ℝ)*D+9),Real.exp_pos _,?_⟩
  intro N hN Q hQ
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hfilter : P.filter (fun p : ℕ => (1:ℝ)<p ∧ (p:ℝ)≤N) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hpN,hpp⟩ := Finset.mem_filter.mp hp
    exact ⟨by exact_mod_cast hpp.one_lt,by exact_mod_cast (Finset.mem_Icc.mp hpN).2⟩
  have hsum : (∑ n ∈ Q,omegaReciprocal n) =
      ∑ n ∈ Q,intervalOmegaWeight (3/2) 1 N n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [omegaReciprocal,intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,
      omegaIn_all_factors (hQ n hn).1 (hQ n hn).2]
  have hmass := interval_omega_moment_product (by norm_num : (0:ℝ)≤3/2)
    (by norm_num : (3/2:ℝ)≤3/2) 1 N N Q hQ
  have hprod := interval_euler_product_bound (by norm_num : (0:ℝ)≤3/2)
    (by norm_num : (3/2:ℝ)≤3/2) 1 N N
  change _ ≤ Real.exp ((∑ p ∈ P,(p:ℝ)⁻¹)+
    ((3/2:ℝ)-1)*(∑ p ∈ P.filter (fun p : ℕ => (1:ℝ)<p ∧ (p:ℝ)≤N),(p:ℝ)⁻¹)+9) at hprod
  rw [hfilter] at hprod
  have he : (∑ p ∈ P,(p:ℝ)⁻¹)=primeReciprocalLE N := by
    simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
  have herr := (abs_le.mp (hDerr N (by exact_mod_cast hN))).2
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  calc
    _ = _ := hsum
    _ ≤ _ := hmass.trans hprod
    _ ≤ Real.exp (((3/2:ℝ)*D+9)+(3/2:ℝ)*B N) := by
      apply Real.exp_le_exp.mpr
      rw [he]
      nlinarith
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos hlog]
      congr 1
      unfold B
      congr 1
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCofactorTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The exponential tail needed for the actual smooth-cofactor truncation. -/
theorem smooth_cofactor_rankin {N : ℕ} (hN : 2 ≤ N) (Z : ℝ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N ∧ Z < Real.log n) :
    (∑ n ∈ Q, (n.totient : ℝ)⁻¹) ≤
      Real.exp (-Z/(4*Real.log N))*(primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hσ : 0 < σ := by dsimp [σ] <;> positivity
  calc
    _ ≤ Real.exp (-σ*Z)*∑ n ∈ Q, (n : ℝ)^σ/(n.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hφ : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (hQ n hn).1
      have hm : 1 ≤ Real.exp (-σ*Z)*(n : ℝ)^σ := by
        rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith [(hQ n hn).2.2])
      have hh := mul_le_mul_of_nonneg_right hm (inv_pos.mpr hφ).le
      simpa only [one_mul,div_eq_mul_inv,mul_assoc] using hh
    _ ≤ Real.exp (-σ*Z)*(primeEulerProduct N)^4 :=
      mul_le_mul_of_nonneg_left (smooth_cofactor_power_mass hN Q (fun n hn =>
        ⟨(hQ n hn).1,(hQ n hn).2.1⟩)) (Real.exp_pos _).le
    _ = _ := by congr 2; dsimp [σ] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCountingSplit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite counting version of the elementary smooth-number Rankin bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma card_le_endpoint_reciprocal (Q : Finset ℕ) (x : ℝ)
    (hQ : ∀ n ∈ Q,0 < n ∧ (n:ℝ) ≤ x) :
    (Q.card:ℝ) ≤ x*(∑ n ∈ Q,(n:ℝ)⁻¹) := by
  rw [Finset.mul_sum]
  calc
    (Q.card:ℝ) = ∑ _n ∈ Q,(1:ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (hQ n hn).1
      exact (one_le_div hn0).mpr (hQ n hn).2

lemma smooth_counting_split {K : ℕ} (hK : 2 ≤ K) (N : ℕ) (Z : ℝ)
    (Q : Finset ℕ) (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  let A : Finset ℕ := Q.filter (fun n : ℕ => (n:ℝ) ≤ Real.exp Z)
  let D : Finset ℕ := Q.filter (fun n : ℕ => ¬(n:ℝ) ≤ Real.exp Z)
  have hA : (A.card:ℝ) ≤ Real.exp Z := by
    have hs : A ⊆ Finset.Icc 1 ⌊Real.exp Z⌋₊ := by
      intro n hn
      obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(hQ n hn).1,Nat.le_floor hh⟩
    have hh : A.card ≤ ⌊Real.exp Z⌋₊ := by simpa using Finset.card_le_card hs
    exact (show (A.card:ℝ) ≤ (⌊Real.exp Z⌋₊:ℝ) by exact_mod_cast hh).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hD := card_le_endpoint_reciprocal D N (by
    intro n hn
    have hh := hQ n (Finset.mem_filter.mp hn).1
    exact ⟨hh.1,by exact_mod_cast hh.2.1⟩)
  have hrec : (∑ n ∈ D,(n:ℝ)⁻¹) ≤ ∑ n ∈ D,(n.totient:ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 := (hQ n (Finset.mem_filter.mp hn).1).1
    apply (inv_le_inv₀ (by exact_mod_cast hn0)
      (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr
    exact_mod_cast Nat.totient_le n
  have htail := smooth_cofactor_rankin hK Z D (by
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    have hz : Real.exp Z < (n:ℝ) := lt_of_not_ge hh
    exact ⟨(hQ n hn).1,(hQ n hn).2.2,(Real.lt_log_iff_exp_lt (by exact_mod_cast (hQ n hn).1)).mpr hz⟩)
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(D.card:ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s:=Q) (p:=fun n => (n:ℝ) ≤ Real.exp Z)).symm
  rw [hcard]
  have hh := mul_le_mul_of_nonneg_left (hrec.trans htail) (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ Real.exp Z+(N*(Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4)) :=
      add_le_add hA (hD.trans hh)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullOmegaTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large-normality-parameter range from the full factor-count moment. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma full_factor_tail_weight {S : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 2*B S ≤ (n.primeFactorsList.length:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp (-2*B S*Real.log (3/2:ℝ))*omegaReciprocal n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (-2*B S*Real.log (3/2:ℝ))*(3/2:ℝ)^n.primeFactorsList.length := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3/2),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [omegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

lemma full_factor_tail_mass : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 1 < S → ∀ N : ℕ,
    2 ≤ N → 0 ≤ B N → 6*B N ≤ B S → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 2*B S ≤ (n.primeFactorsList.length:ℝ)) →
    (Q.card:ℝ) ≤ C*N/Real.log N*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hmoment⟩ := full_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro S hS N hN hBN hBS Q hQ
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hm := hmoment N hN Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hrec : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (-2*B S*Real.log (3/2:ℝ))*(∑ n ∈ Q,omegaReciprocal n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => full_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
  have hexp : Real.exp (-2*B S*Real.log (3/2:ℝ))*(Real.log N)^(3/2:ℝ) ≤
      (Real.log N)⁻¹*(Real.log S)^(-1/6:ℝ) := by
    have hinv : (Real.log N)⁻¹ = Real.exp (-B N) := by
      rw [Real.exp_neg,B,Real.exp_log hlog]
    rw [Real.rpow_def_of_pos hlog,Real.rpow_def_of_pos hlogS,
      hinv,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold B at *
    have hs : 0 ≤ Real.log (Real.log S) := by linarith
    nlinarith [log_three_halves_lower]
  have hcard := card_le_endpoint_reciprocal Q N (fun n hn =>
    ⟨(hQ n hn).1,by exact_mod_cast (hQ n hn).2.1⟩)
  calc
    _ ≤ N*(Real.exp (-2*B S*Real.log (3/2:ℝ))*(C*(Real.log N)^(3/2:ℝ))) :=
      hcard.trans (mul_le_mul_of_nonneg_left (hrec.trans
        (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)) (Nat.cast_nonneg N))
    _ = C*N*(Real.exp (-2*B S*Real.log (3/2:ℝ))*(Real.log N)^(3/2:ℝ)) := by ring
    _ ≤ C*N*((Real.log N)⁻¹*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityPrimeRemoval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a failed normality condition to the cofactor after one prime is removed. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_prime_cofactor {b q : ℕ} (hb : b≠0) (hq : q.Prime)
    (hp : (b*q+1).Prime) (S : ℝ) (hbad : ¬IsNormalPrime S (b*q+1)) :
    2*B S-1 < (omegaIn b 1 S:ℝ) ∨
      ∃ U T : ℝ, S≤U ∧ U<T ∧ T≤(b*q:ℕ) ∧
        Real.sqrt (B S*B T)-1≤|(omegaIn b U T:ℝ)-(B T-B U)| := by
  simp only [IsNormalPrime,hp,true_and,Nat.add_sub_cancel,not_and_or] at hbad
  rcases hbad with hsmall|hinterval
  · left
    have hh := (omegaIn_remove_prime hb hq 1 S).2
    have hhR : (omegaIn (b*q) 1 S:ℝ)≤(omegaIn b 1 S:ℝ)+1 := by exact_mod_cast hh
    push Not at hsmall
    linarith
  · right
    push Not at hinterval
    obtain ⟨U,T,hSU,hUT,hT,hh⟩ := hinterval
    exact ⟨U,T,hSU,hUT,hT,prime_removal_deviation hb hq U T (B T-B U)
      (Real.sqrt (B S*B T)) hh⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargestPrimeCofactor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual largest-prime/cofactor decomposition for a nonnormal prime. -/
noncomputable section
namespace TotientAsymptotic

lemma largestPrimeFactor_mem {n : ℕ} (hn : 2 ≤ n) : largestPrimeFactor n ∈ n.primeFactors := by
  have he := (Nat.nonempty_primeFactors).mpr (show 1 < n by omega)
  have hm := Finset.sup_mem_of_nonempty (f:=id) he
  obtain ⟨p,hp,hpmax⟩ := hm
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  unfold largestPrimeFactor
  change p = n.primeFactors.sup id at hpmax
  rw [← hpmax,max_eq_right (show 1 ≤ p by omega)]
  exact hp

lemma nonnormal_largest_cofactor {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S)
    {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hbad : ¬IsNormalPrime S p) :
    ∃ b q : ℕ,0 < b ∧ q.Prime ∧ q=largestPrimeFactor (p-1) ∧
      p=b*q+1 ∧ b ≤ N ∧ AbnormalCofactor S N b := by
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact hbad (normal_two hS hBS)
  have hpm : 2 ≤ p-1 := by have := hp.two_le; omega
  let q := largestPrimeFactor (p-1)
  have hqm := largestPrimeFactor_mem hpm
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hqd : q ∣ p-1 := Nat.dvd_of_mem_primeFactors hqm
  let b := (p-1)/q
  have hbq : b*q=p-1 := Nat.div_mul_cancel hqd
  have hb0 : 0 < b := by
    by_contra hh
    have hbz : b=0 := Nat.eq_zero_of_not_pos hh
    rw [hbz,zero_mul] at hbq
    omega
  have hpEq : p=b*q+1 := by omega
  have hbN : b ≤ N := by
    have h1 : b ≤ b*q := Nat.le_mul_of_pos_right b hq.pos
    omega
  have hco := nonnormal_prime_cofactor (Nat.ne_of_gt hb0) hq
    (by rwa [← hpEq]) S (by rwa [← hpEq])
  refine ⟨b,q,hb0,hq,rfl,hpEq,hbN,?_⟩
  rcases hco with hs|⟨U,T,hSU,hUT,hT,hh⟩
  · exact Or.inl hs
  · refine Or.inr ⟨U,T,hSU,hUT,hT.trans ?_,hh⟩
    exact_mod_cast (show b*q ≤ N by omega)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeFactorNormalityCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting actual nonnormal primes with a sufficiently large final prime factor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normality_large_factor_card {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (N : ℕ) :
    (normalityLargeFactorPrimes S N).card ≤
      ∑ b ∈ normalityCofactors S N,(allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).card := by
  classical
  let Q := normalityCofactors S N
  let F := fun b => (allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).image (fun q => b*q+1)
  have hcover : normalityLargeFactorPrimes S N ⊆ Q.biUnion F := by
    intro p hp
    obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
    obtain ⟨b,q,hb,hq,hqeq,hpeq,hbN,hco⟩ := nonnormal_largest_cofactor hS hBS hprime hpN hbad
    have hbR : (0:ℝ) < b := by exact_mod_cast hb
    have hprod : (b:ℝ)*q ≤ N := by exact_mod_cast (show b*q ≤ N by omega)
    have hqcut : normalityPrimeCutoff N ≤ q := by rwa [hqeq]
    have hbQ : b ∈ Q := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hb,hbN⟩,
        (mul_le_mul_of_nonneg_left hqcut hbR.le).trans hprod,hco⟩
    have hqX : q ≤ ⌊(N:ℝ)/b⌋₊ := by
      apply (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg N) hbR.le)).mpr
      exact (le_div_iff₀ hbR).mpr (by nlinarith)
    have hqF : q ∈ allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊ :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.pos,hqX⟩,hq,by rwa [← hpeq]⟩
    exact Finset.mem_biUnion.mpr ⟨b,hbQ,Finset.mem_image.mpr ⟨q,hqF,hpeq.symm⟩⟩
  calc
    _ ≤ (Q.biUnion F).card := Finset.card_le_card hcover
    _ ≤ ∑ b ∈ Q,(F b).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun b _ => Finset.card_image_le)

 theorem normality_large_factor_count : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ,
    2 < S → 4 ≤ B S → ∀ N : ℕ, Real.exp 2 ≤ N → 1 ≤ B N →
    1 ≤ Real.log N/(200*B N) →
    ((normalityLargeFactorPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hpair⟩ := cofactor_sieve_cutoff_mass
  obtain ⟨D,hD,hmass⟩ := abnormal_cofactor_mass
  refine ⟨C*D,by positivity,?_⟩
  intro S hS hBS N hN hBN hL
  let Q := normalityCofactors S N
  have hB : 0 < B N := by linarith
  have hNexp1 : Real.exp 1 ≤ (N:ℝ) := (Real.exp_le_exp.mpr (by norm_num)).trans hN
  have hlog : 0 < Real.log N := by
    have hx0 := (Real.exp_pos 2).trans_le hN
    have hh := (Real.le_log_iff_exp_le hx0).mpr hN
    linarith
  have hp := hpair N hN hB hL Q (by
    intro b hb
    obtain ⟨hb,hcut,_⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp hb).1,hcut⟩)
  have hm := hmass S hS hBS N hNexp1 hBN Q (by
    intro b hb
    obtain ⟨hb,_,hco⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp hb).1,(Finset.mem_Icc.mp hb).2,hco⟩)
  have hc : ((normalityLargeFactorPrimes S N).card:ℝ) ≤
      ∑ b ∈ Q,((allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).card:ℝ) := by
    exact_mod_cast normality_large_factor_card (by linarith : 1 < S) (by linarith : 0 ≤ B S) N
  calc
    _ ≤ _ := hc.trans hp
    _ ≤ (C*N*(B N)^3/(Real.log N)^2)*(D*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualFactorCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-factor counts in actual residual totients, including a repeated
last prime in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omega_count_le_log {n : ℕ} (hn : 0 < n) :
    (n.primeFactorsList.length : ℝ) ≤ 2*Real.log n := by
  have hnat : (2 : ℕ)^n.primeFactorsList.length ≤ n := by
    calc
      _ ≤ n.primeFactorsList.prod := List.pow_card_le_prod _ 2
        (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
      _ = n := Nat.prod_primeFactorsList hn.ne'
  have hp : (2 : ℝ)^n.primeFactorsList.length ≤ n := by exact_mod_cast hnat
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<2^n.primeFactorsList.length) hp
  rw [Real.log_pow] at hh
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n.primeFactorsList.length : (0 : ℝ) ≤ n.primeFactorsList.length)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityLargeParameter
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal parameter range: all primes are normal once log S exceeds the endpoint. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma omegaIn_le_length (n : ℕ) (U T : ℝ) :
    omegaIn n U T ≤ n.primeFactorsList.length := List.length_filter_le _ _

lemma normalPrime_of_log_parameter {S : ℝ} (hS : 2 < S) {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ≤ n) (hlarge : (n:ℝ) ≤ Real.log S) :
    IsNormalPrime S p := by
  have hSpos : 0 < S := by linarith
  have hNpos : (0:ℝ) < n := by exact_mod_cast hn
  have hlogN : Real.log n ≤ B S := Real.log_le_log hNpos hlarge
  have hpm : 0 < p-1 := by have := hp.two_le; omega
  have hlogp : Real.log (p-1:ℕ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hpm) (by exact_mod_cast (show p-1 ≤ n by omega))
  refine ⟨hp,?_,?_⟩
  · have hΩ : (omegaIn (p-1) 1 S:ℝ) ≤ (p-1).primeFactorsList.length := by
      exact_mod_cast omegaIn_le_length (p-1) 1 S
    have hh := omega_count_le_log hpm
    linarith
  · intro U T hSU hUT hT
    have he : (n:ℝ)+1 ≤ S := by
      calc
        _ ≤ Real.exp (n:ℝ) := Real.add_one_le_exp _
        _ ≤ Real.exp (Real.log S) := Real.exp_le_exp.mpr hlarge
        _ = S := Real.exp_log hSpos
    have hpmN : (p-1:ℕ) ≤ n := by omega
    have hpmR : ((p-1:ℕ):ℝ) ≤ n := by exact_mod_cast hpmN
    linarith

theorem nonNormalPrimes_empty_of_large_parameter {S : ℝ} (hS : 2 < S) {n : ℕ}
    (hn : 1 ≤ n) (hlarge : (n:ℝ) ≤ Real.log S) : nonNormalPrimes S n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpN,hbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hpN
  exact hbad (normalPrime_of_log_parameter hS hn hprime hle hlarge)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySmallParameter
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary parameter range in Ford's exceptional-prime estimate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma prime_count_global_upper : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 < n →
    (Nat.primeCounting n : ℝ) ≤ C*n/Real.log n := by
  have hev : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (Real.log 4+1)*n/Real.log n := by
    have h := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
    simpa only [Nat.floor_natCast] using h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  let C := max (Real.log 4+1) (2*Real.log (N+4:ℕ))
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < Real.log (4:ℝ)+1) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro n hn
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hn'
  apply (le_div_iff₀ hlog).mpr
  by_cases hlarge : N ≤ n
  · have hh := (le_div_iff₀ hlog).mp (hN n hlarge)
    have hC' : Real.log 4+1 ≤ C := le_max_left _ _
    have hnc : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  · have hcount : (Nat.primeCounting n : ℝ) ≤ 2*n := by
      have hh : Nat.primeCounting n ≤ n+1 := Nat.count_le Nat.Prime
      exact_mod_cast (show Nat.primeCounting n ≤ 2*n by omega)
    have hnK : (n:ℝ) ≤ (N+4:ℕ) := by exact_mod_cast (show n ≤ N+4 by omega)
    have hlogK := Real.log_le_log (by linarith : (0:ℝ)<n) hnK
    have hC' : 2*Real.log (N+4:ℕ) ≤ C := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_right hcount hlog.le
    nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]

lemma doubleLog_nat_pos {n : ℕ} (hn : 3 < n) : 0 < B n := by
  unfold B
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ)<n)).mpr
  have hn' : (3:ℝ) < n := by exact_mod_cast hn
  exact Real.exp_one_lt_three.trans hn'

lemma normality_small_parameter_factor {S : ℝ} (hS : 2 < S) {n : ℕ} (hn : 3 < n)
    (hsmall : Real.log S ≤ (B n)^30) :
    1 ≤ (B n)^5*(Real.log S)^(-1/6:ℝ) := by
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hB := doubleLog_nat_pos hn
  have hroot : (Real.log S)^(1/6:ℝ) ≤ (B n)^5 := by
    calc
      _ ≤ ((B n)^30)^(1/6:ℝ) := Real.rpow_le_rpow hlog.le hsmall (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
        norm_num
  rw [show (-1/6:ℝ) = -(1/6:ℝ) by norm_num, Real.rpow_neg hlog.le]
  exact (one_le_div (Real.rpow_pos_of_pos hlog _)).mpr hroot

/-- The desired exceptional-prime estimate holds throughout the small-S range
using only Chebyshev's bound. The hard range is isolated rather than assumed. -/
theorem normality_small_parameter : ∃ C : ℝ, 0 < C ∧
    ∀ S : ℝ, 2 < S → ∀ n : ℕ, 3 < n → Real.log S ≤ (B n)^30 →
      ((nonNormalPrimes S n).card : ℝ) ≤
        C*n/Real.log n*(B n)^5*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := prime_count_global_upper
  refine ⟨C,hC,?_⟩
  intro S hS n hn hsmall
  have hcount : ((nonNormalPrimes S n).card:ℝ) ≤ Nat.primeCounting n := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun p => ¬IsNormalPrime S p) (Nat.primesLE n))
    rw [Nat.primesLE_card_eq_primeCounting] at hh
    exact_mod_cast hh
  apply hcount.trans ((hbound n hn).trans _)
  have hf := normality_small_parameter_factor hS hn hsmall
  have hbase : 0 ≤ C*n/Real.log n := by
    apply div_nonneg (by positivity)
    exact (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hh := mul_le_mul_of_nonneg_left hf hbase
  simpa only [mul_one,mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityBoundedEndpoint
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform absorption of the finitely many bounded counting endpoints. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_card_le_twice (S : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ((nonNormalPrimes S N).card:ℝ) ≤ 2*N := by
  classical
  have hsub : nonNormalPrimes S N ⊆ Nat.primesLE N := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hc := Finset.card_le_card hsub
  have hp : Nat.primeCounting N ≤ N+1 := Nat.count_le Nat.Prime
  rw [Nat.primesLE_card_eq_primeCounting] at hc
  exact_mod_cast (show (nonNormalPrimes S N).card ≤ 2*N by omega)

lemma normality_bounded_endpoint (M : ℕ) (hM : 4 ≤ M) : ∃ C : ℝ, 0 < C ∧
    ∀ S : ℝ, 2 < S → ∀ N : ℕ, 3 < N → N ≤ M →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  let C := 2*Real.log M*(M:ℝ)^(1/6:ℝ)/(B 4)^5
  have hB4 : 0 < B 4 := by exact doubleLog_nat_pos (n:=4) (by norm_num)
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro S hS N hN hNM
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogNM : Real.log N ≤ Real.log M := Real.log_le_log hN0 (by exact_mod_cast hNM)
  have hBN : B 4 ≤ B N := Real.log_le_log (Real.log_pos (by norm_num : (1:ℝ) < 4))
    (Real.log_le_log (by norm_num : (0:ℝ) < 4) (by exact_mod_cast (show 4 ≤ N by omega)))
  have hBpos : 0 < B N := hB4.trans_le hBN
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  by_cases hlarge : (N:ℝ) ≤ Real.log S
  · rw [nonNormalPrimes_empty_of_large_parameter hS (by omega) hlarge]
    simp only [Finset.card_empty,Nat.cast_zero]
    dsimp [C]
    positivity
  · have hSM : Real.log S ≤ (M:ℝ) := (le_of_not_ge hlarge).trans (by exact_mod_cast hNM)
    have hr := Real.rpow_le_rpow hlogS.le hSM (by norm_num : (0:ℝ) ≤ 1/6)
    have hpow := pow_le_pow_left₀ hB4.le hBN 5
    have h1 : 1 ≤ Real.log M/Real.log N := (one_le_div hlogN).mpr hlogNM
    have h2 : 1 ≤ (B N)^5/(B 4)^5 := (one_le_div (pow_pos hB4 5)).mpr hpow
    have h3 : 1 ≤ (M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ) :=
      (one_le_div (Real.rpow_pos_of_pos hlogS _)).mpr hr
    have hprod : 1 ≤ (Real.log M/Real.log N)*((B N)^5/(B 4)^5)*
        ((M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ)) := by
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    have he : C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) =
        (2*N)*((Real.log M/Real.log N)*((B N)^5/(B 4)^5)*
          ((M:ℝ)^(1/6:ℝ)/(Real.log S)^(1/6:ℝ))) := by
      rw [show (-1/6:ℝ)=-(1/6:ℝ) by norm_num,Real.rpow_neg hlogS.le]
      dsimp [C]
      ring
    rw [he]
    exact (nonnormal_card_le_twice S N (by omega)).trans
      (by have hh := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 2*N by positivity); simpa using hh)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySmoothCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth shifted integers below the normality sieve cutoff. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_smooth_count : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    Real.exp 2 ≤ N → 1 ≤ B N → 1 ≤ Real.log N/(200*B N) →
    ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ (largestPrimeFactor n:ℝ) ≤ normalityPrimeCutoff N) →
    (Q.card:ℝ) ≤ C*N/(Real.log N)^2 := by
  obtain ⟨C,hC,hM⟩ := mertensProductInput
  refine ⟨8+C^4,by positivity,?_⟩
  intro N hN hBN hL Q hQ
  have hB : 0 < B N := by linarith
  have hN0 : (0:ℝ) < N := (Real.exp_pos 2).trans_le hN
  have hlog2 : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hN
  have hlog : 0 < Real.log N := by linarith
  let K := ⌊normalityPrimeCutoff N⌋₊
  have hcut : Real.exp (2*(Real.log N/(200*B N))) = normalityPrimeCutoff N := by
    unfold normalityPrimeCutoff
    congr 1
    ring
  have hK : 2 ≤ K := (floor_log_endpoint hL hcut.le).1
  have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hKupper : Real.log K ≤ Real.log N/(100*B N) := by
    have hh := Real.log_le_log hK0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [normalityPrimeCutoff,Real.log_exp] using hh
  have hKL : Real.log K ≤ Real.log N := by
    apply hKupper.trans
    apply (div_le_iff₀ (by positivity : 0 < 100*B N)).mpr
    nlinarith
  have hCprod : primeEulerProduct K ≤ C*Real.log N :=
    (hM K hK).trans (mul_le_mul_of_nonneg_left hKL hC.le)
  have he : Real.exp (-(Real.log N/2)/(4*Real.log K)) ≤ Real.exp (-10*B N) := by
    apply Real.exp_le_exp.mpr
    have hu := (le_div_iff₀ (by positivity : 0 < 100*B N)).mp hKupper
    have hl : 10*B N ≤ (Real.log N/2)/(4*Real.log K) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*Real.log K)).mpr
      nlinarith [mul_nonneg hB.le hlogK.le]
    rw [neg_div]
    linarith
  have htail : Real.exp (-(Real.log N/2)/(4*Real.log K))*(primeEulerProduct K)^4 ≤
      C^4/(Real.log N)^2 := by
    have hprod : (primeEulerProduct K)^4 ≤ (C*Real.log N)^4 :=
      pow_le_pow_left₀ (primeEulerProduct_pos K).le hCprod 4
    apply (mul_le_mul he hprod (by positivity) (Real.exp_pos _).le).trans
    apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
    calc
      _ = C^4*(Real.exp (-10*B N)*(Real.exp (B N))^6) := by
        rw [show Real.exp (B N)=Real.log N from Real.exp_log hlog]
        ring
      _ = C^4*Real.exp (-4*B N) := by
        rw [← Real.exp_nat_mul,← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ C^4 := by
        have hh := Real.exp_le_one_iff.mpr (show -4*B N ≤ 0 by linarith)
        nlinarith [show 0 ≤ C^4 by positivity]
  have hsmall : Real.exp (Real.log N/2) ≤ 8*N/(Real.log N)^2 := by
    have hquad := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ Real.log N/2)
    have hh : (Real.log N)^2 ≤ 8*Real.exp (Real.log N/2) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (Real.log N/2)).le
    have hexp : Real.exp (Real.log N/2)*Real.exp (Real.log N/2) = (N:ℝ) := by
      rw [← Real.exp_add,add_halves,Real.exp_log hN0]
    rw [mul_assoc,hexp] at hmul
    apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
    nlinarith
  have hsplit := smooth_counting_split hK N (Real.log N/2) Q (by
    intro n hn
    obtain ⟨hn0,hnN,hsm⟩ := hQ n hn
    exact ⟨hn0,hnN,Nat.le_floor hsm⟩)
  have hmult := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ Real.exp (Real.log N/2)+N*(Real.exp (-(Real.log N/2)/(4*Real.log K))*(primeEulerProduct K)^4) := by
      convert hsplit using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ 8*N/(Real.log N)^2+N*(C^4/(Real.log N)^2) := add_le_add hsmall hmult
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityComplement
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary primes are counted by their smooth predecessors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normality_complement_count : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ N : ℕ,
    Real.exp 2 ≤ N → 1 ≤ B N → 1 ≤ Real.log N/(200*B N) →
    ((normalitySmallFactorPrimes S N).card:ℝ) ≤ C*N/(Real.log N)^2 := by
  classical
  obtain ⟨C,hC,hsmooth⟩ := normality_smooth_count
  refine ⟨C,hC,?_⟩
  intro S N hN hB hL
  let P := normalitySmallFactorPrimes S N
  let Q := P.image (fun p => p-1)
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp r hr he
    change p-1=r-1 at he
    have hp2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2.two_le
    have hr2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).2.two_le
    omega
  have hcard : Q.card=P.card := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  apply hsmooth N hN hB hL Q
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
  exact ⟨by have := hprime.two_le; omega,by omega,(le_of_not_ge hcut)⟩

lemma nonNormalPrimes_card_split (S : ℝ) (N : ℕ) :
    (nonNormalPrimes S N).card =
      (normalityLargeFactorPrimes S N).card+(normalitySmallFactorPrimes S N).card := by
  classical
  exact (Finset.card_filter_add_card_filter_not (s:=nonNormalPrimes S N)
    (p:=fun p => normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))).symm

lemma normality_middle_scale {S : ℝ} (hS : 1 < S) {N : ℕ} (hB : 1 ≤ B N)
    (hlogN : 0 < Real.log N) (hSupper : Real.log S ≤ (Real.log N)^6) :
    (N:ℝ)/(Real.log N)^2 ≤ N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  have hroot : (Real.log S)^(1/6:ℝ) ≤ Real.log N := by
    calc
      _ ≤ ((Real.log N)^6)^(1/6:ℝ) :=
        Real.rpow_le_rpow (Real.log_pos hS).le hSupper (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hlogN.le]
        norm_num
  have hinv : (Real.log N)⁻¹ ≤ (Real.log S)^(-1/6:ℝ) := by
    rw [show (-1/6:ℝ) = -(1/6:ℝ) by norm_num,Real.rpow_neg (Real.log_pos hS).le]
    exact (inv_le_inv₀ hlogN (Real.rpow_pos_of_pos (Real.log_pos hS) _)).mpr hroot
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hpow : 1 ≤ (B N)^5 := one_le_pow₀ hB
  calc
    _ = (N/Real.log N)*(Real.log N)⁻¹ := by ring
    _ ≤ (N/Real.log N)*(Real.log S)^(-1/6:ℝ) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ N/Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
      nlinarith

 theorem normality_middle_parameter : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ,
    2 < S → 4 ≤ B S → ∀ N : ℕ, Real.exp 2 ≤ N → 1 ≤ B N →
    1 ≤ Real.log N/(200*B N) → Real.log S ≤ (Real.log N)^6 →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hlarge⟩ := normality_large_factor_count
  obtain ⟨D,hD,hsmall⟩ := normality_complement_count
  refine ⟨C+D,by positivity,?_⟩
  intro S hS hBS N hN hB hL hupper
  have hlog : 0 < Real.log N := by
    have hn0 := (Real.exp_pos 2).trans_le hN
    have hh := (Real.le_log_iff_exp_le hn0).mpr hN
    linarith
  have hscale := mul_le_mul_of_nonneg_left
    (normality_middle_scale (by linarith : 1 < S) hB hlog hupper) hD.le
  have hs : ((normalitySmallFactorPrimes S N).card:ℝ) ≤
      D*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
    calc
      _ ≤ D*N/(Real.log N)^2 := hsmall S N hN hB hL
      _ = D*(N/(Real.log N)^2) := by ring
      _ ≤ D*(N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)) := hscale
      _ = _ := by ring
  have he : ((nonNormalPrimes S N).card:ℝ) =
      ((normalityLargeFactorPrimes S N).card:ℝ)+((normalitySmallFactorPrimes S N).card:ℝ) := by
    exact_mod_cast nonNormalPrimes_card_split S N
  rw [he]
  have hl := hlarge S hS hBS N hN hB hL
  calc
    _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)+
        D*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := add_le_add hl hs
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityLargeScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large S makes interval normality vacuous, leaving the full factor-count tail. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_full_factor_excess {S : ℝ} {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hSN : (N:ℝ) ≤ S) (hbad : ¬IsNormalPrime S p) :
    2*B S ≤ ((p-1).primeFactorsList.length:ℝ) := by
  have hsmall : ¬(omegaIn (p-1) 1 S:ℝ) ≤ 2*B S := by
    intro hs
    apply hbad
    refine ⟨hp,hs,?_⟩
    intro U T hSU hUT hT
    have hpm : ((p-1:ℕ):ℝ) < N := by exact_mod_cast (show p-1 < N by have := hp.two_le; omega)
    linarith
  have hcount : omegaIn (p-1) 1 S ≤ (p-1).primeFactorsList.length := List.length_filter_le _ _
  have hcountR : (omegaIn (p-1) 1 S:ℝ) ≤ (p-1).primeFactorsList.length := by exact_mod_cast hcount
  linarith

 theorem normality_large_scale : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S →
    ∀ N : ℕ, 3 < N → 1 ≤ B N → (Real.log N)^6 ≤ Real.log S →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hfull⟩ := full_factor_tail_mass
  refine ⟨C,hC,?_⟩
  intro S hS N hN hB hSlarge
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hBS : 6*B N ≤ B S := by
    have hh := Real.log_le_log (pow_pos hlog 6) hSlarge
    simpa only [Real.log_pow,B,Nat.cast_ofNat] using hh
  have hSN : (N:ℝ) ≤ S := by
    have hb : B N ≤ B S := by linarith
    have hl := (Real.log_le_log_iff hlog hlogS).mp hb
    exact (Real.log_le_log_iff hN0 (by linarith : 0 < S)).mp hl
  let Q : Finset ℕ := (nonNormalPrimes S N).image (fun p => p-1)
  have hcard : Q.card = (nonNormalPrimes S N).card := by
    apply Finset.card_image_iff.mpr
    intro p hp r hr he
    change p-1=r-1 at he
    have hp2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.two_le
    have hr2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2.two_le
    omega
  have hb := hfull S (by linarith) N (by omega) (by linarith) hBS Q (by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨by have := hprime.two_le; omega,by omega,nonnormal_full_factor_excess hprime hpN hSN hbad⟩)
  rw [hcard] at hb
  apply hb.trans
  have hpow : 1 ≤ (B N)^5 := one_le_pow₀ hB
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ C*N/Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityThreshold
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit elementary conditions above one fixed endpoint threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_threshold_conditions {N : ℕ} (hN : 3 < N) (hB : 400 ≤ B N) :
    Real.exp 2 ≤ (N:ℝ) ∧ 1 ≤ B N ∧ 1 ≤ Real.log N/(200*B N) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ B N by linarith)
  rw [show Real.exp (B N)=Real.log N from Real.exp_log hlog] at hquad
  have hlogbig : 200*B N ≤ Real.log N := by
    nlinarith [mul_nonneg (show 0 ≤ B N by linarith) (show 0 ≤ B N-400 by linarith)]
  refine ⟨(Real.le_log_iff_exp_le hN0).mp (by nlinarith),by linarith,?_⟩
  exact (one_le_div (show 0 < 200*B N by positivity)).mpr hlogbig

lemma normality_large_S_threshold {N : ℕ} {S : ℝ} (hB : 400 ≤ B N)
    (hsmall : (B N)^30 ≤ Real.log S) : 4 ≤ B S := by
  have hB0 : 0 < B N := by linarith
  have he : Real.exp 1 ≤ B N := Real.exp_one_lt_three.le.trans (by linarith)
  have hl : 1 ≤ Real.log (B N) := (Real.le_log_iff_exp_le hB0).mpr he
  have hh := Real.log_le_log (pow_pos hB0 30) hsmall
  rw [Real.log_pow] at hh
  change 30*Real.log (B N) ≤ B S at hh
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityInput
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unconditional proof of the precise exceptional-prime estimate used from
Ford, The distribution of totients, Lemma 2.6. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

 theorem fordLemma26Input_oai : FordLemma26Input := by
  obtain ⟨C,hC,hsmall⟩ := normality_small_parameter
  obtain ⟨D,hD,hmiddle⟩ := normality_middle_parameter
  obtain ⟨E,hE,hlarge⟩ := normality_large_scale
  have hevent : ∀ᶠ N : ℕ in atTop, 400 ≤ B N :=
    (B_tendsto.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 400)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  obtain ⟨F,hF,hfinite⟩ := normality_bounded_endpoint (max M 4) (le_max_right _ _)
  refine ⟨C+D+E+F,by positivity,?_⟩
  intro S hS N hN
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hB : 0 < B N := doubleLog_nat_pos hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let W := (N:ℝ)/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have liftBound (K : ℝ) (hK : K ≤ C+D+E+F)
      (hk : ((nonNormalPrimes S N).card:ℝ) ≤ K*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)) :
      ((nonNormalPrimes S N).card:ℝ) ≤
        (C+D+E+F)*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
    have hmono := mul_le_mul_of_nonneg_right hK hW
    calc
      _ ≤ K*W := by
        convert hk using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [W]
        ring
      _ ≤ (C+D+E+F)*W := hmono
      _ = _ := by dsimp [W] <;> ring
  by_cases hNM : N ≤ max M 4
  · exact liftBound F (by linarith) (hfinite S hS N hN hNM)
  · have hBN : 400 ≤ B N := hM N (by omega)
    by_cases hs : Real.log S ≤ (B N)^30
    · exact liftBound C (by linarith) (hsmall S hS N hN hs)
    · have hBS := normality_large_S_threshold hBN (le_of_not_ge hs)
      obtain ⟨hx,hb,hl⟩ := normality_threshold_conditions hN hBN
      by_cases hm : Real.log S ≤ (Real.log N)^6
      · exact liftBound D (by linarith) (hmiddle S hS hBS N hx hb hl hm)
      · exact liftBound E (by linarith) (hlarge S hS N hN hb (le_of_not_ge hm))

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.fordLemma26Input_oai := @OAI.TotientAsymptotic.fordLemma26Input_oai
