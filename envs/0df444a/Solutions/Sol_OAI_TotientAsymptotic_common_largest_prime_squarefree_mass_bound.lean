-- Prove2me | solution 1 for OAI.TotientAsymptotic.common_largest_prime_squarefree_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:33:01.985212+00:00
-- url     : https://prove2.me/submissions/2757813a-135a-43fd-afa3-ec078ea80fc9

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Analysis.PSeries
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
import Mathlib.Data.Nat.Squarefree
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
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_AuxResults
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)


theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl


end Aux
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Basic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)

local notation3 "g" => SelbergSieve.selbergTerms s

section SieveLemmas

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x,
        Nat.sum_divisorsAntidiagonal' fun x _ => g x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]

  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors P) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end SelbergSieve
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Selberg
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l (fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/g l * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      exact (mul_le_of_le_one_left (abs_nonneg <| γ d2) (s.selberg_bound_weights d1)).trans
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ X * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
end
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeBands
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-factor bands derived from normality, including the small-prime case. -/

noncomputable section

namespace TotientAsymptotic

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) : largestPrimeFactor n ≤ n := by
  apply largestPrimeFactor_le_of_prime_divisors hn
  intro p _ hp hn0
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteSieveMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite product mass and its first logarithmic moment for the Selberg denominator. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma subset_weight_moment (S : Finset ℕ) (w l : ℕ → ℝ)
    (hw : ∀ p ∈ S,0 ≤ w p) :
    (∑ T ∈ S.powerset,(∏ p ∈ T,w p)*(∑ p ∈ T,l p)) =
      (∏ p ∈ S,(1+w p))*(∑ p ∈ S,w p*l p/(1+w p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hwS : ∀ p ∈ S,0 ≤ w p := fun p hp => hw p (Finset.mem_insert_of_mem hp)
    have ha0 := hw a (Finset.mem_insert_self _ _)
    have hne : 1+w a ≠ 0 := by linarith
    have hnew : (∑ T ∈ S.powerset,(∏ p ∈ insert a T,w p)*(∑ p ∈ insert a T,l p)) =
        w a*l a*(∑ T ∈ S.powerset,∏ p ∈ T,w p)+
          w a*(∑ T ∈ S.powerset,(∏ p ∈ T,w p)*(∑ p ∈ T,l p)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [Finset.prod_insert haT,Finset.sum_insert haT]
      ring_nf
    rw [Finset.sum_powerset_insert ha,hnew,← Finset.prod_one_add,ih hwS,
      Finset.prod_insert ha,Finset.sum_insert ha]
    field_simp [hne]
    ring

/-- If the first moment is at most half the cutoff, at least half of the
Euler-product mass comes from subsets below that cutoff. -/
lemma subset_weight_below_half (S : Finset ℕ) (w l : ℕ → ℝ)
    (hw : ∀ p ∈ S,0 ≤ w p) (hl : ∀ p ∈ S,0 ≤ l p)
    {L : ℝ} (hL : 0 < L)
    (hmean : (∑ p ∈ S,w p*l p/(1+w p)) ≤ L/2) :
    (∏ p ∈ S,(1+w p))/2 ≤
      ∑ T ∈ S.powerset,if (∑ p ∈ T,l p) ≤ L then (∏ p ∈ T,w p) else 0 := by
  classical
  have hwT (T : Finset ℕ) (hT : T ∈ S.powerset) : 0 ≤ ∏ p ∈ T,w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hT hp))
  have hlT (T : Finset ℕ) (hT : T ∈ S.powerset) : 0 ≤ ∑ p ∈ T,l p :=
    Finset.sum_nonneg (fun p hp => hl p (Finset.mem_powerset.mp hT hp))
  have hpoint : ∀ T ∈ S.powerset,L*(∏ p ∈ T,w p) ≤
      L*(if (∑ p ∈ T,l p) ≤ L then (∏ p ∈ T,w p) else 0)+
        (∏ p ∈ T,w p)*(∑ p ∈ T,l p) := by
    intro T hT
    split_ifs with hsmall
    · nlinarith [mul_nonneg (hwT T hT) (hlT T hT)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) (hwT T hT)
      nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.prod_one_add,
    subset_weight_moment S w l hw] at hsum
  have hprod : 0 ≤ ∏ p ∈ S,(1+w p) := Finset.prod_nonneg (fun p hp => by have := hw p hp; linarith)
  have hm := mul_le_mul_of_nonneg_left hmean hprod
  nlinarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothResidualMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler product bounds the entire smooth residual-integer sum. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_reciprocal_norm_lt_one {p : ℕ} (hp : p.Prime) : ‖reciprocalNatHom p‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [reciprocalNatHom,MonoidHom.coe_mk,OneHom.coe_mk,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)] using (inv_lt_one₀ (zero_lt_one.trans hpR)).mpr hpR

lemma reciprocal_prime_factor (p : ℕ) (hp : p.Prime) :
    (1-reciprocalNatHom p)⁻¹=(p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (1-(p : ℝ)⁻¹)⁻¹=(p : ℝ)/(p-1)
  field_simp

/-- Only positivity and smoothness are used; the residuals may repeat prime
factors and the upper cutoff on their size is arbitrary. -/
theorem smooth_residual_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ primeEulerProduct N := by
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
  have hsum : (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ T, reciprocalNatHom n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    change (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ Q.attach, (n.val : ℝ)⁻¹
    exact (Finset.sum_attach Q (fun n : ℕ => (n : ℝ)⁻¹)).symm
  have hseries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun {_} hp => prime_reciprocal_norm_lt_one hp) S
  calc
    _ = ∑ n ∈ T, reciprocalNatHom n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, reciprocalNatHom n := by
      apply hseries.1.of_norm.sum_le_tsum
      intro n _
      change 0 ≤ (n.val : ℝ)⁻¹
      positivity
    _ = ∏ p ∈ S with p.Prime, (1-reciprocalNatHom p)⁻¹ := hseries.2.tsum_eq
    _ = primeEulerProduct N := by
      apply Finset.prod_congr rfl
      intro p hp
      exact reciprocal_prime_factor p (Finset.mem_filter.mp hp).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SieveEulerProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary lower bounds for the sieve Euler product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeEulerProduct_log_lower (N : ℕ) : Real.log N ≤ primeEulerProduct N := by
  have h := smooth_residual_reciprocal_mass N (Finset.Icc 1 N) (by
    intro n hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hn
    exact ⟨hn1,(largestPrimeFactor_le_self hn1).trans hnN⟩)
  have he : (∑ n ∈ Finset.Icc 1 N,(n:ℝ)⁻¹) = (harmonic N:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [he] at h
  have hl := log_le_harmonic_floor (N:ℝ) (Nat.cast_nonneg N)
  simp only [Nat.floor_natCast] at hl
  exact hl.trans h

lemma oddEulerProduct_eq (z : ℕ) (hz : 2 ≤ z) :
    primeEulerProduct z = 2 * ∏ p ∈ oddSievePrimes z,(p:ℝ)/(p-1) := by
  classical
  have htwo : 2 ∈ (Finset.Icc 2 z).filter Nat.Prime := by norm_num [hz]
  have hs : oddSievePrimes z = ((Finset.Icc 2 z).filter Nat.Prime).erase 2 := by
    ext p
    simp only [mem_oddSievePrimes,Finset.mem_erase,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hpz,hpp,hp2⟩
      exact ⟨hp2,⟨hpp.two_le,hpz⟩,hpp⟩
    · rintro ⟨hp2,⟨_,hpz⟩,hpp⟩
      exact ⟨hpz,hpp,hp2⟩
  rw [hs,primeEulerProduct,← Finset.mul_prod_erase _ _ htwo]
  norm_num

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PeriodicSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval errors for the periodic congruence classes in the sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma count_periodic_blocks (d : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (q r : ℕ) :
    Nat.count P (q*d+r) = q*Nat.count P d+Nat.count P r := by
  have hshift (q : ℕ) : (fun k => P (q*d+k)) = P := by
    funext k
    apply propext
    rw [hP (q*d+k)]
    simp only [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_mod]
    exact (hP k).symm
  have hblocks : Nat.count P (q*d)=q*Nat.count P d := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul,Nat.count_add,ih]
      simp only [hshift]
      ring
  rw [Nat.count_add,hblocks]
  simp only [hshift]

lemma count_periodic_error (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (N : ℕ) :
    |(Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ)| ≤ d := by
  have hsplit : N=(N/d)*d+N%d := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm
  have hc : Nat.count P N=(N/d)*Nat.count P d+Nat.count P (N%d) := by
    conv_lhs => rw [hsplit]
    exact count_periodic_blocks d P hP (N/d) (N%d)
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hr : ((N%d:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have htail : (Nat.count P (N%d):ℝ) ≤ ((N%d:ℕ):ℝ) := by exact_mod_cast Nat.count_le P
  have hmass : (Nat.count P d:ℝ) ≤ d := by exact_mod_cast Nat.count_le P
  have hfrac : ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) ≤ ((N%d:ℕ):ℝ) := by
    calc
      _ ≤ ((N%d:ℕ):ℝ)/d*d := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := div_mul_cancel₀ _ hdR.ne'
  have hid : (Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ) =
      (Nat.count P (N%d):ℝ)-((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by
    rw [hc]
    push_cast
    have hNr : (N:ℝ)=(N/d:ℕ)* (d:ℝ)+(N%d:ℕ) := by exact_mod_cast hsplit
    rw [hNr]
    field_simp
    ring
  rw [hid]
  apply abs_le.mpr
  constructor
  · have hnon : (0:ℝ) ≤ Nat.count P (N%d) := Nat.cast_nonneg _
    linarith
  · have hnon : (0:ℝ) ≤ ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by positivity
    linarith

lemma interval_count_discrepancy (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    |(((Finset.Icc 1 N).filter P).card:ℝ)-(Nat.count P N:ℝ)| ≤ 1 := by
  have hupper : ((Finset.Icc 1 N).filter P).card ≤ Nat.count P N+1 := by
    have hs : (Finset.Icc 1 N).filter P ⊆ (Finset.range (N+1)).filter P := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega),hP⟩
    have hh := Finset.card_le_card hs
    rw [← Nat.count_eq_card_filter_range,Nat.count_succ] at hh
    split_ifs at hh <;> omega
  have hlower : Nat.count P N ≤ ((Finset.Icc 1 N).filter P).card+1 := by
    have hs : (Finset.range N).filter P ⊆ insert 0 ((Finset.Icc 1 N).filter P) := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      by_cases hz : n=0
      · simp [hz]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨by omega,by have := Finset.mem_range.mp hn; omega⟩,hP⟩
    have hh := (Finset.card_le_card hs).trans (Finset.card_insert_le 0 _)
    rwa [← Nat.count_eq_card_filter_range] at hh
  have hu : (((Finset.Icc 1 N).filter P).card:ℝ) ≤ (Nat.count P N:ℝ)+1 := by exact_mod_cast hupper
  have hl : (Nat.count P N:ℝ) ≤ (((Finset.Icc 1 N).filter P).card:ℝ)+1 := by exact_mod_cast hlower
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveRoots
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local three-linear-form sieve in Ford's collision argument. -/
noncomputable section
namespace TotientAsymptotic

lemma tripleSieveRoots_card_eq_three (p a b : ℕ) [Fact p.Prime]
    (ha : ¬p ∣ a) (hb : ¬p ∣ b) (hab : (a:ZMod p) ≠ b) :
    (tripleSieveRoots p a b).card = 3 := by
  have ha0 : (a:ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff a p).not.mpr ha
  have hb0 : (b:ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hb
  have hinv : -(a:ZMod p)⁻¹ ≠ -(b:ZMod p)⁻¹ := by
    intro h
    apply hab
    exact inv_injective (neg_injective h)
  rw [tripleSieveRoots_eq_union,shiftedSieveRoots_of_not_dvd p a ha,
    shiftedSieveRoots_of_not_dvd p b hb]
  have he : ({0,-(a:ZMod p)⁻¹} ∪ {0,-(b:ZMod p)⁻¹} : Finset (ZMod p)) =
      {0,-(a:ZMod p)⁻¹,-(b:ZMod p)⁻¹} := by ext r; simp
  rw [he]
  simp [Finset.card_insert_of_notMem,ha0,hb0,hinv]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveCRT
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact CRT and interval discrepancies for the three-form collision sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma tripleRootCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (a b : ℕ) :
    tripleRootCount (m*n) a b = tripleRootCount m a b*tripleRootCount n a b := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero n := ⟨hn⟩
  let e := ZMod.chineseRemainder hcop
  have he (r : ZMod (m*n)) : r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1)=0 ↔
      (e r).1*((a:ZMod m)*(e r).1+1)*((b:ZMod m)*(e r).1+1)=0 ∧
      (e r).2*((a:ZMod n)*(e r).2+1)*((b:ZMod n)*(e r).2+1)=0 := by
    calc
      _ ↔ e (r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1))=0 := e.map_eq_zero_iff.symm
      _ ↔ _ := by
        simp only [map_mul,map_add,map_natCast,map_one,Prod.ext_iff]
        rfl
  let ep : {r : ZMod (m*n) // r*((a:ZMod (m*n))*r+1)*((b:ZMod (m*n))*r+1)=0} ≃
      {r : ZMod m × ZMod n //
        r.1*((a:ZMod m)*r.1+1)*((b:ZMod m)*r.1+1)=0 ∧
        r.2*((a:ZMod n)*r.2+1)*((b:ZMod n)*r.2+1)=0} :=
    e.toEquiv.subtypeEquiv he
  let ee := ep.trans (Equiv.subtypeProdEquivProd
    (p := fun r : ZMod m => r*((a:ZMod m)*r+1)*((b:ZMod m)*r+1)=0)
    (q := fun r : ZMod n => r*((a:ZMod n)*r+1)*((b:ZMod n)*r+1)=0))
  unfold tripleRootCount
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact (Fintype.card_congr ee).trans (Fintype.card_prod _ _)

lemma tripleRootCount_eq_count (d a b : ℕ) (hd : 0 < d) :
    tripleRootCount d a b = Nat.count (fun q => d ∣ tripleSievePolynomial a b q) d := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let e : {q : ℕ // q<d ∧ d ∣ tripleSievePolynomial a b q} ≃
      {r : ZMod d // r*((a:ZMod d)*r+1)*((b:ZMod d)*r+1)=0} := {
    toFun := fun q => ⟨q.val,by
      have hh := (ZMod.natCast_eq_zero_iff (tripleSievePolynomial a b q.val) d).mpr q.property.2
      simpa only [tripleSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh⟩
    invFun := fun r => ⟨r.val.val,ZMod.val_lt r.val,by
      apply (ZMod.natCast_eq_zero_iff (tripleSievePolynomial a b r.val.val) d).mp
      simpa only [tripleSievePolynomial,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        ZMod.natCast_zmod_val] using r.property⟩
    left_inv := fun q => by apply Subtype.ext; exact ZMod.val_natCast_of_lt q.property.1
    right_inv := fun r => by apply Subtype.ext; exact ZMod.natCast_zmod_val r.val }
  let _ : Fintype {q : ℕ // q<d ∧ d ∣ tripleSievePolynomial a b q} :=
    Nat.CountSet.fintype (fun q => d ∣ tripleSievePolynomial a b q) d
  rw [Nat.count_eq_card_fintype]
  exact (Nat.card_congr e).symm.trans Nat.card_eq_fintype_card

lemma tripleSievePolynomial_mod (a b d q : ℕ) :
    tripleSievePolynomial a b q % d = tripleSievePolynomial a b (q%d) % d := by
  simp [tripleSievePolynomial,Nat.add_mod,Nat.mul_mod]

lemma tripleSieve_count_error (a b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(Nat.count (fun q => d ∣ tripleSievePolynomial a b q) N:ℝ)-
      (N:ℝ)/d*(tripleRootCount d a b:ℝ)| ≤ d := by
  rw [tripleRootCount_eq_count d a b hd]
  apply count_periodic_error d hd
  intro q
  simp only [Nat.dvd_iff_mod_eq_zero,tripleSievePolynomial_mod a b d q]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete Selberg sieve for q, aq+1 and bq+1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleSievePolynomial_strictMono (a b : ℕ) : StrictMono (tripleSievePolynomial a b) := by
  intro q r hqr
  have ha : a*q+1 ≤ a*r+1 := Nat.add_le_add_right (Nat.mul_le_mul_left a hqr.le) 1
  have hb : b*q+1 ≤ b*r+1 := Nat.add_le_add_right (Nat.mul_le_mul_left b hqr.le) 1
  have hp : 0 < (a*r+1)*(b*r+1) := Nat.mul_pos (by omega) (by omega)
  calc
    tripleSievePolynomial a b q = q*((a*q+1)*(b*q+1)) := by unfold tripleSievePolynomial; ring
    _ ≤ q*((a*r+1)*(b*r+1)) := Nat.mul_le_mul_left q (Nat.mul_le_mul ha hb)
    _ < r*((a*r+1)*(b*r+1)) := Nat.mul_lt_mul_of_pos_right hqr hp
    _ = tripleSievePolynomial a b r := by unfold tripleSievePolynomial; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveDenominator
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma tripleSieveWeight_nonneg (a b : ℕ) {z p : ℕ} (hp : p ∈ tripleSievePrimes z) :
    0 ≤ tripleSieveWeight a b p := by
  obtain ⟨_,hpp,hp2⟩ := mem_tripleSievePrimes.mp hp
  exact div_nonneg (tripleSieveDensity_positive a b p hpp).le
    (sub_pos.mpr (tripleSieveDensity_lt_one a b p hpp hp2)).le

lemma tripleSieveWeight_moment (a b : ℕ) {z p : ℕ} (hp : p ∈ tripleSievePrimes z) :
    tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p) =
      tripleSieveDensity a b p * Real.log p := by
  obtain ⟨_,hpp,hp2⟩ := mem_tripleSievePrimes.mp hp
  have hn : 1-tripleSieveDensity a b p ≠ 0 :=
    (sub_pos.mpr (tripleSieveDensity_lt_one a b p hpp hp2)).ne'
  have hn' : 1+tripleSieveWeight a b p ≠ 0 := by
    have := tripleSieveWeight_nonneg a b hp
    linarith
  unfold tripleSieveWeight
  field_simp
  ring

lemma tripleSieve_moment_le (a b z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ tripleSievePrimes z,
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p)) ≤
        3*Real.log 4*(2+Real.log z) := by
  have hpoint (p : ℕ) (hp : p ∈ tripleSievePrimes z) :
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p) ≤
        3*(Real.log p/(p:ℝ)) := by
    obtain ⟨_,hpp,_⟩ := mem_tripleSievePrimes.mp hp
    rw [tripleSieveWeight_moment a b hp,tripleSieveDensity_prime a b p hpp]
    let _ : Fact p.Prime := ⟨hpp⟩
    rw [tripleRootCount_eq_card]
    have hc : ((tripleSieveRoots p a b).card:ℝ) ≤ 3 := by
      exact_mod_cast tripleSieveRoots_card_le p a b
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hh := mul_le_mul_of_nonneg_right hc (div_nonneg hl hp0.le)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

  calc
    _ ≤ ∑ p ∈ tripleSievePrimes z,3*(Real.log p/(p:ℝ)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,3*(Real.log p/(p:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpz,hpp,_⟩ := mem_tripleSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le,hpz⟩,hpp⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact mul_nonneg (by norm_num) (div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      nlinarith [prime_log_mass_le z hz]

lemma tripleSieveTerms_prod (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ tripleSievePrimes z) :
    selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,tripleSieveWeight a b p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_tripleSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_tripleSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change tripleSieveDensity a b p * (1/(1-tripleSieveDensity a b p)) = _
  simp [tripleSieveWeight,div_eq_mul_inv]

lemma tripleSieveBoundingSum_powerset (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (triplePrimeSieve a b X z y hy) =
      ∑ T ∈ (tripleSievePrimes z).powerset,
        if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,tripleSieveWeight a b p else 0 := by
  classical
  have hsq := tripleSievePrimes_squarefree z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ tripleSievePrimes z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ tripleSievePrimes z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p : ℕ):ℝ)^2 ≤ y then
      selbergTerms (triplePrimeSieve a b X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_tripleSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [tripleSieveTerms_prod a b X z y hy T (Finset.mem_powerset.mp hT)]

/-- The logarithmic first moment confines at least half of the Euler product to
integers within the square-root cutoff used by Selberg's denominator. -/
theorem tripleSieveBoundingSum_lower (a b X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 12*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))/2 ≤
      selbergBoundingSum (triplePrimeSieve a b X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y / 2 := by positivity
  have hm : (∑ p ∈ tripleSievePrimes z,
      tripleSieveWeight a b p * Real.log p / (1+tripleSieveWeight a b p)) ≤
        (Real.log y/2)/2 := by
    nlinarith [tripleSieve_moment_le a b z hz]
  have hh := subset_weight_below_half (tripleSievePrimes z) (tripleSieveWeight a b)
    (fun p => Real.log p) (fun p hp => tripleSieveWeight_nonneg a b hp)
    (fun p hp => Real.log_nonneg (by
      exact_mod_cast (mem_tripleSievePrimes.mp hp).2.1.one_lt.le)) hl hm
  apply hh.trans
  rw [tripleSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_tripleSievePrimes.mp (hTp hp)).2.1
  have hpos : (0:ℝ) < (∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hlog : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
    rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
  split_ifs with hsmall hcut hcut
  · exact le_rfl
  · exfalso
    apply hcut
    apply (Real.log_le_log_iff (sq_pos_of_pos hpos) (by linarith : 0<y)).mp
    rw [Real.log_pow,hlog]
    norm_num
    linarith
  · exact Finset.prod_nonneg (fun p hp => tripleSieveWeight_nonneg a b (hTp hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleDiscriminant
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exactly the primes dividing ab(b-a) can merge roots of the three forms. -/
noncomputable section
namespace TotientAsymptotic

lemma tripleDiscriminant_pos {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    0 < tripleDiscriminant a b :=
  Nat.mul_pos (Nat.mul_pos ha (ha.trans hab)) (Nat.sub_pos_of_lt hab)

lemma tripleRootCount_of_not_dvd {a b p : ℕ} (hab : a < b) (hp : p.Prime)
    (hd : ¬p ∣ tripleDiscriminant a b) : tripleRootCount p a b = 3 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have ha : ¬p ∣ a := fun h => hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) (b-a))
  have hb : ¬p ∣ b := fun h => hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) (b-a))
  have hdiff : ¬p ∣ b-a := fun h => hd (dvd_mul_of_dvd_right h (a*b))
  have hneq : (a:ZMod p) ≠ b := by
    intro he
    apply hdiff
    apply (ZMod.natCast_eq_zero_iff (b-a) p).mp
    rw [Nat.cast_sub hab.le,he,sub_self]
  rw [tripleRootCount_eq_card]
  exact tripleSieveRoots_card_eq_three p a b ha hb hneq

lemma tripleRootCount_bounds (a b p : ℕ) (hp : p.Prime) :
    1 ≤ tripleRootCount p a b ∧ tripleRootCount p a b ≤ 3 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleRootCount_eq_card]
  exact ⟨Finset.card_pos.mpr ⟨0,zero_mem_tripleSieveRoots p a b⟩,tripleSieveRoots_card_le p a b⟩

lemma tripleSieveWeight_euler_factor {a b p : ℕ} (hab : a < b) (hp : p.Prime)
    (hp3 : 3 < p) : ((p:ℝ)/(p-1))^3 ≤
      (1+tripleSieveWeight a b p)*
        (if p ∣ tripleDiscriminant a b then ((p:ℝ)/(p-1))^2 else 1) := by
  have hpR : (3:ℝ) < p := by exact_mod_cast hp3
  have hb := tripleRootCount_bounds a b p hp
  have hk1 : (1:ℝ) ≤ tripleRootCount p a b := by exact_mod_cast hb.1
  have hk3 : (tripleRootCount p a b:ℝ) ≤ 3 := by exact_mod_cast hb.2
  have he : 1+tripleSieveWeight a b p = (p:ℝ)/(p-tripleRootCount p a b) := by
    rw [tripleSieveWeight,tripleSieveDensity_prime a b p hp]
    field_simp [show (p:ℝ)-(tripleRootCount p a b:ℝ) ≠ 0 by linarith]
    ring
  rw [he]
  split_ifs with hd
  · have hsingle : (p:ℝ)/(p-1) ≤ (p:ℝ)/(p-tripleRootCount p a b) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hh := mul_le_mul_of_nonneg_right hsingle (sq_nonneg ((p:ℝ)/(p-1)))
    nlinarith
  · rw [tripleRootCount_of_not_dvd hab hp hd,mul_one]
    norm_num only [Nat.cast_ofNat]
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos (by linarith : (0:ℝ) < p-1) 3) (by linarith)).mpr
    nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleEulerProduct
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-three lower bound for the collision sieve's Euler product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleEulerProduct_eq (z : ℕ) (hz : 3 ≤ z) :
    primeEulerProduct z = 3*∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1) := by
  classical
  have hthree : 3 ∈ oddSievePrimes z := by norm_num [mem_oddSievePrimes,hz]
  have hs : tripleSievePrimes z = (oddSievePrimes z).erase 3 := by
    ext p
    simp only [mem_tripleSievePrimes,mem_oddSievePrimes,Finset.mem_erase]
    constructor
    · rintro ⟨hpz,hpp,hp3⟩
      exact ⟨by omega,hpz,hpp,by omega⟩
    · rintro ⟨hp3,hpz,hpp,hp2⟩
      have hp := hpp.two_le
      exact ⟨hpz,hpp,by omega⟩
  rw [oddEulerProduct_eq z (by omega),hs,← Finset.mul_prod_erase _ _ hthree]
  norm_num
  ring

lemma tripleEulerProduct_log_lower (z : ℕ) (hz : 3 ≤ z) :
    Real.log z/3 ≤ ∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1) := by
  have h := primeEulerProduct_log_lower z
  rw [tripleEulerProduct_eq z hz] at h
  linarith

lemma triple_exceptional_product_le_totient {D : ℕ} (hD : 0 < D) (z : ℕ) :
    (∏ p ∈ tripleSievePrimes z,if p ∣ D then ((p:ℝ)/(p-1))^2 else 1) ≤
      ((D:ℝ)/D.totient)^2 := by
  classical
  have hp : (∏ p ∈ (tripleSievePrimes z).filter (fun p => p ∣ D),(p:ℝ)/(p-1)) ≤
      (D:ℝ)/D.totient := by
    rw [totient_ratio_product hD]
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(mem_tripleSievePrimes.mp hp).2.1,hd,hD.ne'⟩
    · intro p hp
      have hpp := (mem_tripleSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1
      have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.one_lt
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp _
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      apply (le_div_iff₀ (by linarith : (0:ℝ) < p-1)).mpr
      linarith
  rw [← Finset.prod_filter,Finset.prod_pow]
  apply pow_le_pow_left₀ _ hp 2
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ) < p := by
    exact_mod_cast (mem_tripleSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1.one_lt
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

lemma tripleSieveEulerProduct_lower {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (z : ℕ) (hz : 3 ≤ z) :
    (Real.log z)^3/27 ≤ (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))*
      ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by
  have hfactor : (∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1))^3 ≤
      (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))*
        (∏ p ∈ tripleSievePrimes z,if p ∣ tripleDiscriminant a b then ((p:ℝ)/(p-1))^2 else 1) := by
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      have hpR : (3:ℝ) < p := by exact_mod_cast (mem_tripleSievePrimes.mp hp).2.2
      exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith)) 3
    · intro p hp
      exact tripleSieveWeight_euler_factor hab (mem_tripleSievePrimes.mp hp).2.1
        (mem_tripleSievePrimes.mp hp).2.2
  have hp : 0 ≤ ∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p) :=
    Finset.prod_nonneg (fun p hp => by have := tripleSieveWeight_nonneg a b hp; linarith)
  have he := mul_le_mul_of_nonneg_left
    (triple_exceptional_product_le_totient (tripleDiscriminant_pos ha hab) z) hp
  have hl := pow_le_pow_left₀ (show 0 ≤ Real.log z/3 by
    have hz1 : (1:ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    exact div_nonneg (Real.log_nonneg hz1) (by norm_num))
    (tripleEulerProduct_log_lower z hz) 3
  calc
    _ = (Real.log z/3)^3 := by ring
    _ ≤ _ := hl
    _ ≤ _ := hfactor.trans he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleDensity
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative residue proportions for the three-form sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleRootCount_one (a b : ℕ) : tripleRootCount 1 a b = 1 := by
  rw [tripleRootCount_eq_count 1 a b (by norm_num),Nat.count_one]
  simp [tripleSievePolynomial]

lemma tripleRootCount_prod (a b : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) :
    tripleRootCount (∏ p ∈ S,p) a b = ∏ p ∈ S,tripleRootCount p a b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tripleRootCount_one a b
  | @insert p S hp ih =>
    have hprime := hS p (Finset.mem_insert_self _ _)
    have hS' : ∀ q ∈ S,q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S,q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hprime.coprime_iff_not_dvd.mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hprime (hS' q hq)).mp hd
      exact hp (he ▸ hq)
    rw [Finset.prod_insert hp,tripleRootCount_mul hprime.ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS' q hq).ne_zero)) hcop,
      ih hS',Finset.prod_insert hp]

lemma tripleRootCount_density (a b d : ℕ) (hd : Squarefree d) :
    (tripleRootCount d a b:ℝ) = d*tripleSieveDensity a b d := by
  classical
  have hprod : ∏ p ∈ d.primeFactors,p = d := Nat.prod_primeFactors_of_squarefree hd
  have hcount : tripleRootCount d a b = ∏ p ∈ d.primeFactors,tripleRootCount p a b := by
    conv_lhs => rw [← hprod]
    exact tripleRootCount_prod a b d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hdensity : tripleSieveDensity a b d =
      ∏ p ∈ d.primeFactors,(tripleRootCount p a b:ℝ)/p :=
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero
  calc
    _ = ∏ p ∈ d.primeFactors,(tripleRootCount p a b:ℝ) := by rw [hcount,Nat.cast_prod]
    _ = ∏ p ∈ d.primeFactors,(p:ℝ)*((tripleRootCount p a b:ℝ)/p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib,hdensity,← Nat.cast_prod,hprod]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual simultaneous primes counted by the three-form sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma triplePrimeTuples_coprime {a b X z q : ℕ} (hq : q ∈ triplePrimeTuples a b X z) :
    (∏ p ∈ tripleSievePrimes z,p).Coprime (tripleSievePolynomial a b q) := by
  obtain ⟨_,hq,ha,hb,hzq,hza,hzb⟩ := Finset.mem_filter.mp hq
  apply Nat.coprime_of_dvd
  intro p hp hpd hpv
  have hpz := (mem_tripleSievePrimes.mp (mem_tripleSievePrimes_of_dvd hp hpd)).1
  change p ∣ q*(a*q+1)*(b*q+1) at hpv
  rcases hp.dvd_mul.mp hpv with hqa|hb'
  · rcases hp.dvd_mul.mp hqa with hq'|ha'
    · have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hq'
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp ha).mp ha'
      omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp hb).mp hb'
    omega

lemma triplePrimeTuples_le_sifted (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((triplePrimeTuples a b X z).card:ℝ) ≤
      siftedSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) := by
  let f := tripleSievePolynomial a b
  have hinj := (tripleSievePolynomial_strictMono a b).injective
  have hsubset : (triplePrimeTuples a b X z).image f ⊆
      ((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ tripleSievePrimes z,p).Coprime n) := by
    intro n hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,rfl⟩,
      triplePrimeTuples_coprime hq⟩
  have hh := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinj] at hh
  have he : siftedSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) =
      (((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ tripleSievePrimes z,p).Coprime n)).card := by
    change (∑ d ∈ (Finset.Icc 1 X).image f,
      if (∏ p ∈ tripleSievePrimes z,p).Coprime d then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hh

lemma triplePrimeSieve_multSum (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    multSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ) := by
  simp only [multSum,triplePrimeSieve]
  rw [Finset.sum_image]
  · simp only [Finset.sum_boole]
  · exact fun r _ s _ h => (tripleSievePolynomial_strictMono _ _).injective h

lemma triplePrimeSieve_rem_le (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) {d : ℕ}
    (hd : Squarefree d) :
    |rem (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d| ≤ d+1 := by
  rw [rem,triplePrimeSieve_multSum]
  change |(((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ)-
    tripleSieveDensity a b d*(X:ℝ)| ≤ d+1
  have he : (X:ℝ)/d*(tripleRootCount d a b:ℝ) = tripleSieveDensity a b d*(X:ℝ) := by
    rw [tripleRootCount_density a b d hd]
    field_simp [show (d:ℝ) ≠ 0 by exact_mod_cast hd.ne_zero]
  rw [← he]
  calc
    _ ≤ |(((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ)-
          (Nat.count (fun q => d ∣ tripleSievePolynomial a b q) X:ℝ)|+
        |(Nat.count (fun q => d ∣ tripleSievePolynomial a b q) X:ℝ)-
          (X:ℝ)/d*(tripleRootCount d a b:ℝ)| := abs_sub_le _ _ _
    _ ≤ 1+d := add_le_add (interval_count_discrepancy _ X)
      (tripleSieve_count_error a b d (Nat.pos_of_ne_zero hd.ne_zero) X)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveError
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial bound for the complete error term of the concrete Selberg sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma triple_sieve_divisor_weight {z d : ℕ} (hd : d ∣ ∏ p ∈ tripleSievePrimes z,p) :
    (3:ℕ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
  have hsq := (tripleSievePrimes_squarefree z).squarefree_of_dvd hd
  have hlen : ArithmeticFunction.cardDistinctFactors d ≤ d.primeFactorsList.length :=
    d.primeFactorsList.dedup_sublist.length_le
  calc
    _ ≤ 3^d.primeFactorsList.length := Nat.pow_le_pow_right (by norm_num) hlen
    _ ≤ d.primeFactorsList.prod := List.pow_card_le_prod _ 3 (by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactorsList hp
      have hmem := mem_tripleSievePrimes_of_dvd hprime ((Nat.dvd_of_mem_primeFactorsList hp).trans hd)
      have hh := mem_tripleSievePrimes.mp hmem
      exact hh.2.2.le)
    _ = d := Nat.prod_primeFactorsList hsq.ne_zero

lemma triplePrimeSieve_error_sum (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ (∏ p ∈ tripleSievePrimes z,p).divisors,
      if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
        |rem (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d| else 0) ≤ 2*y^3 := by
  classical
  let P : ℕ := ∏ p ∈ tripleSievePrimes z,p
  let T : Finset ℕ := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ y)
  have hP := tripleSievePrimes_squarefree z
  have hT (d : ℕ) (hd : d∈T) : d∣P ∧ 1≤d ∧ (d:ℝ)≤y := by
    obtain ⟨hd,hy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd,hP0⟩ := Nat.mem_divisors.mp hd
    have h0 : d≠0 := by
      intro h
      subst d
      exact hP0 (zero_dvd_iff.mp hd)
    exact ⟨hd,Nat.one_le_iff_ne_zero.mpr h0,hy⟩
  have hcard : (T.card:ℝ) ≤ y := by
    have hsub : T ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro d hd
      have hh := hT d hd
      exact Finset.mem_Icc.mpr ⟨hh.2.1,Nat.le_floor hh.2.2⟩
    have hh := Finset.card_le_card hsub
    have hc : (T.card:ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast (by simpa using hh : T.card ≤ ⌊y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter]
  change (∑ d ∈ T,(3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
      |rem (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d|) ≤ _
  calc
    _ ≤ ∑ _d ∈ T,2*y^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd,h1,hdy⟩ := hT d hd
      have hweight : (3:ℝ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
        exact_mod_cast triple_sieve_divisor_weight hd
      have hrem := triplePrimeSieve_rem_le a b X z y hy (hP.squarefree_of_dvd hd)
      have hdR : (1:ℝ)≤d := by exact_mod_cast h1
      have hh := mul_le_mul hweight hrem (abs_nonneg _) (by positivity : (0:ℝ)≤d)
      nlinarith
    _ = (T.card:ℝ)*(2*y^2) := by simp
    _ ≤ y*(2*y^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- All arithmetic remainders in the three-linear-form sieve are now eliminated. -/
theorem triplePrimeTuples_bound (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((triplePrimeTuples a b X z).card:ℝ) ≤
      X/selbergBoundingSum (triplePrimeSieve a b X z y hy)+2*y^3 :=
  (triplePrimeTuples_le_sifted a b X z y hy).trans
    ((selberg_bound_simple (triplePrimeSieve a b X z y hy)).trans
      (add_le_add le_rfl (triplePrimeSieve_error_sum a b X z y hy)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TriplePrimeBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elimination of Selberg's auxiliary quantities in the three-form bound. -/
noncomputable section
open scoped BigOperators
open SelbergSieve
namespace TotientAsymptotic

lemma triplePrimeTuples_log_bound {a b : ℕ} (ha : 0 < a) (hab : a < b) (X z : ℕ)
    (y : ℝ) (hy : 1 < y) (hz : 3 ≤ z)
    (hscale : 12*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    ((triplePrimeTuples a b X z).card:ℝ) ≤
      54*X*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log z)^3+2*y^3 := by
  let s := triplePrimeSieve a b X z y hy.le
  let P := ∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p)
  let R : ℝ := ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2
  have hR : 0 ≤ R := sq_nonneg _
  have hD : 0 < selbergBoundingSum s := selbergBoundingSum_pos s
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hP : P/2 ≤ selbergBoundingSum s :=
    tripleSieveBoundingSum_lower a b X z y hy (by omega) hscale
  have hprod : (Real.log z)^3/27 ≤ P*R := tripleSieveEulerProduct_lower ha hab z hz
  have hden : (Real.log z)^3 ≤ 54*selbergBoundingSum s*R := by
    have hh := mul_le_mul_of_nonneg_right hP hR
    nlinarith
  have hmain : (X:ℝ)/selbergBoundingSum s ≤ 54*X*R/(Real.log z)^3 := by
    apply (div_le_div_iff₀ hD (pow_pos hlog 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg X : (0:ℝ) ≤ X)
    nlinarith
  exact (triplePrimeTuples_bound a b X z y hy.le).trans (add_le_add hmain le_rfl)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllPrimeTriples
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring small q in the three-form sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma allPrimeTriples_card_le (a b X : ℕ) : (allPrimeTriples a b X).card ≤ X := by
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) (Finset.Icc 1 X))
  simpa [allPrimeTriples] using hh

lemma allPrimeTriples_cutoff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X z : ℕ) :
    (allPrimeTriples a b X).card ≤ (triplePrimeTuples a b X z).card+z := by
  classical
  have hsub : allPrimeTriples a b X ⊆ triplePrimeTuples a b X z ∪ Finset.Icc 1 z := by
    intro q hq
    obtain ⟨hqX,hqp,haq,hbq⟩ := Finset.mem_filter.mp hq
    by_cases hqz : q ≤ z
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqX).1,hqz⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      have hqa : q ≤ a*q := by simpa using Nat.mul_le_mul_right q ha
      have hqb : q ≤ b*q := by simpa using Nat.mul_le_mul_right q hb
      exact ⟨hqX,hqp,haq,hbq,by omega,by omega,by omega⟩
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa using hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientRatioLogLog
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform log-log bound for the elementary totient ratio. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_factor_large_prime {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hL : 0<L) (hpL : L≤p) :
    (p:ℝ)/(p-1) ≤ Real.exp (4*Real.log p/L) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hp1 : (0:ℝ)<p-1 := by linarith
  have hlog : (1/2:ℝ)≤Real.log p := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hp2
    linarith [Real.log_two_gt_d9]
  have hfirst : (1:ℝ)/(p-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  have hsecond : 2/(p:ℝ) ≤ 4*Real.log p/L := by
    apply (div_le_div_iff₀ hp0 hL).mpr
    nlinarith
  have he : (p:ℝ)/(p-1) = 1+1/(p-1) := by field_simp <;> ring
  rw [he]
  have hh := Real.add_one_le_exp (4*Real.log p/L)
  linarith

lemma totient_large_prime_product {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 0<L)
    (hbL : Real.log b ≤ L) (T : Finset ℕ) (hT : T ⊆ b.primeFactors)
    (hlarge : ∀ p ∈ T,L≤p) :
    (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 := by
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
  have hprod0 : (0:ℝ)<(∏ p ∈ T,p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hdvd : (∏ p ∈ T,p) ∣ b :=
    (Finset.prod_dvd_prod_of_subset T b.primeFactors id hT).trans b.prod_primeFactors_dvd
  have hsum : (∑ p ∈ T,Real.log p) ≤ L := by
    have he : Real.log ((∏ p ∈ T,p : ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
      rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
    rw [← he]
    exact (Real.log_le_log hprod0 (by exact_mod_cast Nat.le_of_dvd hb hdvd)).trans hbL
  calc
    _ ≤ ∏ p ∈ T,Real.exp (4*Real.log p/L) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : (1:ℝ)<p := by exact_mod_cast (hprimes p hp).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp
        exact totient_factor_large_prime (hprimes p hp) hL (hlarge p hp)
    _ = Real.exp ((4/L)*(∑ p ∈ T,Real.log p)) := by
      rw [← Real.exp_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum (show 0≤4/L by positivity)
      have he : (4/L)*L=4 := by field_simp
      rwa [he] at hh

/-- Uniformity in `b ≤ x` is the form needed when summing shifted prime pairs. -/
theorem totient_ratio_loglog_bound : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, Real.exp 2 ≤ x →
    ∀ b : ℕ, 0<b → (b:ℝ)≤x → (b:ℝ)/b.totient ≤ C*Real.log (Real.log x) := by
  classical
  obtain ⟨C,hC,hM⟩ := mertensProductInput
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro x hx b hb hbx
  have hx0 : 0<x := (Real.exp_pos 2).trans_le hx
  have hlog : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hN : 2 ≤ ⌊Real.log x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hlog
  let S := b.primeFactors.filter (fun p : ℕ => (p:ℝ)≤Real.log x)
  let T := b.primeFactors.filter (fun p : ℕ => ¬(p:ℝ)≤Real.log x)
  have hsmall : (∏ p ∈ S,(p:ℝ)/(p-1)) ≤ primeEulerProduct ⌊Real.log x⌋₊ := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hpb,hpL⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hpb).two_le,Nat.le_floor hpL⟩,
        Nat.prime_of_mem_primeFactors hpb⟩
    · intro p hp
      have hp1 : (1:ℝ)<p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp _
      have hp1 : (1:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      apply (le_div_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
      linarith
  have hlarge : (∏ p ∈ T,(p:ℝ)/(p-1)) ≤ Real.exp 4 :=
    totient_large_prime_product hb (by linarith)
      (Real.log_le_log (by exact_mod_cast hb) hbx) T (Finset.filter_subset _ _)
      (fun p hp => (le_of_not_ge (Finset.mem_filter.mp hp).2))
  have hsmall0 : 0 ≤ ∏ p ∈ S,(p:ℝ)/(p-1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsplit : (b:ℝ)/b.totient =
      (∏ p ∈ S,(p:ℝ)/(p-1))*(∏ p ∈ T,(p:ℝ)/(p-1)) := by
    rw [totient_ratio_product hb]
    exact (Finset.prod_filter_mul_prod_filter_not b.primeFactors
      (fun p : ℕ => (p:ℝ)≤Real.log x) (fun p => (p:ℝ)/(p-1))).symm
  have hlN : Real.log (⌊Real.log x⌋₊:ℝ) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by exact_mod_cast (show 0<⌊Real.log x⌋₊ by omega))
      (Nat.floor_le (by linarith))
  calc
    (b:ℝ)/b.totient = _ := hsplit
    _ ≤ primeEulerProduct ⌊Real.log x⌋₊ * Real.exp 4 :=
      mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by
        have hp1 : (1:ℝ)<p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)))
        (primeEulerProduct_pos _).le
    _ ≤ (C*Real.log (⌊Real.log x⌋₊:ℝ))*Real.exp 4 :=
      mul_le_mul_of_nonneg_right (hM _ hN) (Real.exp_pos _).le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hlN (show 0≤C*Real.exp 4 by positivity)
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllShiftedPrimePairs
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the small primes removed by the sieve cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_ratio_one_le {b : ℕ} (hb : 0<b) : (1:ℝ)≤(b:ℝ)/b.totient := by
  have hφ : (0:ℝ)<b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
  apply (le_div_iff₀ hφ).mpr
  simpa using (show (b.totient:ℝ)≤b by exact_mod_cast Nat.totient_le b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicCollisionMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite dyadic quotient can be integrated from its actual lowest slice. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma dyadic_nat_bounds {v : ℕ} (hv : 1 < v) :
    1 ≤ Nat.clog 2 v ∧ (2 : ℝ)^(Nat.clog 2 v)/2 < v ∧
      (v : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 v) := by
  have hn : 1 ≤ Nat.clog 2 v := by
    have hh := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2) (x := v) (y := 0)).mpr
      (by simpa using hv)
    omega
  refine ⟨hn,?_,?_⟩
  · have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hv
    have he : Nat.clog 2 v=Nat.clog 2 v-1+1 := by omega
    rw [he,pow_succ]
    have hcast : (2 : ℝ)^(Nat.clog 2 v-1) < v := by exact_mod_cast hh
    convert hcast using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) v

lemma dyadic_endpoint_log (n : ℕ) :
    Real.log ((2 : ℝ)^n)=(n : ℝ)*Real.log 2 := by rw [Real.log_pow]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicCubic
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A convergent reciprocal tail from finite cubic-logarithmic count bounds. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_reciprocal_cube_tail (K L : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc K L,((k:ℝ)^3)⁻¹) ≤ 2/(K:ℝ)^2 := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hsets : Finset.Icc K L=Finset.Ioo (K-1) (L+1) := by ext k; simp; omega
  have hs : (∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) ≤ 2/(K:ℝ) := by
    rw [hsets]
    have hh := sum_Ioo_inv_sq_le (α:=ℝ) (K-1) (L+1)
    have he : ((K-1:ℕ):ℝ)+1=K := by exact_mod_cast (show K-1+1=K by omega)
    rwa [he] at hh
  calc
    _ ≤ ∑ k ∈ Finset.Icc K L,(K:ℝ)⁻¹*((k:ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hh := mul_le_mul_of_nonneg_right (inv_anti₀ hK0 hkK) (inv_nonneg.mpr (sq_nonneg (k:ℝ)))
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = (K:ℝ)⁻¹*(∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ (K:ℝ)⁻¹*(2/K) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hK0.le)
    _ = _ := by ring

lemma finite_dyadic_cubic_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) (K L : ℕ) (hK : 1 ≤ K) {A : ℝ} (hA : 0 ≤ A)
    (hn : ∀ a ∈ Q,n a ∈ Finset.Icc K L)
    (hlo : ∀ a ∈ Q,(2:ℝ)^(n a)/4 ≤ v a)
    (hcount : ∀ k ∈ Finset.Icc K L,((Q.filter (fun a => n a=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^3) :
    (∑ a ∈ Q,(v a)⁻¹) ≤ 8*A/(K:ℝ)^2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (k : ℕ) (hk : k ∈ Finset.Icc K L) :
      (∑ a ∈ Q.filter (fun a => n a=k),(v a)⁻¹) ≤ 4*A*((k:ℝ)^3)⁻¹ := by
    have hy : (0:ℝ) < (2:ℝ)^k := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => n a=k),4/(2:ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
        have hh := hlo a ha
        rw [he] at hh
        simpa only [inv_div] using inv_anti₀ (div_pos hy (by norm_num)) hh
      _ = ((Q.filter (fun a => n a=k)).card:ℝ)*(4/(2:ℝ)^k) := by simp
      _ ≤ (A*(2:ℝ)^k/(k:ℝ)^3)*(4/(2:ℝ)^k) :=
        mul_le_mul_of_nonneg_right (hcount k hk) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc K L,4*A*((k:ℝ)^3)⁻¹ := Finset.sum_le_sum hf
    _ = 4*A*(∑ k ∈ Finset.Icc K L,((k:ℝ)^3)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ 4*A*(2/(K:ℝ)^2) := mul_le_mul_of_nonneg_left (finite_reciprocal_cube_tail K L hK) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicLogTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial summation for logarithmic sieve bounds. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_dyadic_log_range (Q : Finset ℕ) (hQ : Q.Nonempty)
    {U : ℝ} (hU : 1 < U) (hlo : ∀ q ∈ Q,U ≤ q) :
    ∃ K L : ℕ, 1 ≤ K ∧ Real.log U ≤ (K:ℝ)*Real.log 2 ∧
      (∀ q ∈ Q,Nat.clog 2 q ∈ Finset.Icc K L) ∧
      (∀ q ∈ Q,(2:ℝ)^(Nat.clog 2 q)/4 ≤ q) := by
  classical
  let T := Q.image (Nat.clog 2)
  have hT : T.Nonempty := hQ.image _
  let K := T.min' hT
  obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
  have hb := dyadic_nat_bounds hq1
  rw [heq] at hb
  refine ⟨K,Q.sup (Nat.clog 2),hb.1,?_,?_,?_⟩
  · calc
      Real.log U ≤ Real.log (q:ℝ) := Real.log_le_log (zero_lt_one.trans hU) (hlo q hq)
      _ ≤ Real.log ((2:ℝ)^K) := Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hb.2.2
      _ = _ := dyadic_endpoint_log K
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le T _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩),
      Finset.le_sup hq⟩
  · intro q hq
    have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
    have hh := (dyadic_nat_bounds hq1).2.1
    have hp : 0 < (2:ℝ)^(Nat.clog 2 q) := by positivity
    linarith

lemma finite_dyadic_log_cube_tail (Q : Finset ℕ) {U A : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ k : ℕ,1 ≤ k → ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^3) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 8*A*(Real.log 2)^2/(Real.log U)^2 := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_cubic_mass Q (Nat.clog 2) (fun q => (q:ℝ))
      K L hK hA hn hv (fun k hk => hc k (hK.trans (Finset.mem_Icc.mp hk).1))
    have hK0 : (0:ℝ) < K := by exact_mod_cast hK
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hs := pow_le_pow_left₀ hLU.le hlog 2
    apply hh.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hK0) (sq_pos_of_pos hLU)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*A by positivity)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SieveCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit small-power cutoffs for the two-linear-form sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedPrimeCutoff_bounds {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    2 ≤ shiftedPrimeCutoff L ∧
    L/(256*Real.log 4) ≤ Real.log (shiftedPrimeCutoff L) ∧
    Real.log (shiftedPrimeCutoff L) ≤ L/(128*Real.log 4) ∧
    (shiftedPrimeCutoff L:ℝ) ≤ Real.exp (3*L/4) := by
  have hc : 1 ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    linarith
  have hL0 : 0<L := by nlinarith
  have hd : 0<128*Real.log 4 := by positivity
  have hu : 4 ≤ L/(128*Real.log 4) := (le_div_iff₀ hd).mpr (by nlinarith)
  have he2 : (2:ℝ) ≤ Real.exp (L/(128*Real.log 4)) := by
    have hh := Real.add_one_le_exp (L/(128*Real.log 4))
    linarith
  have hz : 2 ≤ shiftedPrimeCutoff L := (Nat.le_floor_iff (by positivity)).mpr he2
  have hz0 : (0:ℝ) < shiftedPrimeCutoff L := by exact_mod_cast (show 0 < shiftedPrimeCutoff L by omega)
  have hfloor := Nat.sub_one_lt_floor (Real.exp (L/(128*Real.log 4)))
  have hhalf : Real.exp (L/(128*Real.log 4))/2 ≤ (shiftedPrimeCutoff L:ℝ) := by
    dsimp [shiftedPrimeCutoff]
    linarith
  have hlower := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp] at hlower
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this
    exact this
  have hfrac : L/(256*Real.log 4) = (L/(128*Real.log 4))/2 := by ring
  refine ⟨hz,?_,?_,?_⟩
  · rw [hfrac]
    linarith
  · have hh := Real.log_le_log hz0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp] using hh
  · apply (Nat.floor_le (Real.exp_pos _).le).trans
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing small-power cutoff also supports sieve dimension three. -/
noncomputable section
namespace TotientAsymptotic

lemma tripleSieveCutoff_three {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    3 ≤ shiftedPrimeCutoff L := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hz := shiftedPrimeCutoff_bounds hL
  have hlow : (2:ℝ) ≤ L/(256*Real.log 4) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp : (0:ℝ) < shiftedPrimeCutoff L := by exact_mod_cast (show 0 < shiftedPrimeCutoff L by omega)
  have hh := Real.log_le_sub_one_of_pos hp
  have hthree : (3:ℝ) ≤ shiftedPrimeCutoff L := by linarith [hz.2.1]
  exact_mod_cast hthree

lemma tripleSieveCutoff_scale {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    12*Real.log 4*(2+Real.log (shiftedPrimeCutoff L)) ≤ Real.log (Real.exp (L/4)) := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hh := (shiftedPrimeCutoff_bounds hL).2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 12*Real.log 4 by positivity)
  have he : 12*Real.log 4*(L/(128*Real.log 4))=3*L/32 := by field_simp <;> ring
  rw [he] at hm
  rw [Real.log_exp]
  nlinarith

lemma tripleSieveCutoff_error {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    (shiftedPrimeCutoff L:ℝ)+2*(Real.exp (L/4))^3 ≤ 1152*Real.exp L/L^3 := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0 < L := by nlinarith
  have he : (Real.exp (L/4))^3 = Real.exp (3*L/4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hcube := Real.pow_div_factorial_le_exp (L/4) (show 0 ≤ L/4 by positivity) 3
  norm_num only [Nat.factorial] at hcube
  have hsmall : L^3 ≤ 384*Real.exp (L/4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3*L/4)).le
  have hsum : Real.exp (L/4)*Real.exp (3*L/4)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : 3*Real.exp (3*L/4) ≤ 1152*Real.exp L/L^3 := by
    apply (le_div_iff₀ (pow_pos hL0 3)).mpr
    rw [mul_assoc,hsum] at hm
    nlinarith
  rw [he]
  exact (by linarith [(shiftedPrimeCutoff_bounds hL).2.2.2] :
    (shiftedPrimeCutoff L:ℝ)+2*Real.exp (3*L/4) ≤ 3*Real.exp (3*L/4)).trans hbound

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrimeTripleBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform upper-bound sieve for the three prime linear forms. -/
noncomputable section
namespace TotientAsymptotic

lemma allPrimeTriples_large_bound {a b X : ℕ} (ha : 0 < a) (hab : a < b)
    (hX : 512*Real.log 4 ≤ Real.log X) :
    ((allPrimeTriples a b X).card:ℝ) ≤
      (54*(256*Real.log 4)^3+1152)*X*
        ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3 := by
  let L := Real.log (X:ℝ)
  let d := 256*Real.log (4:ℝ)
  let R : ℝ := ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hL : 0 < L := by dsimp [L] <;> nlinarith
  have hX0 : (0:ℝ) < X := zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL)
  have hR : 1 ≤ R := by
    have hh := totient_ratio_one_le (tripleDiscriminant_pos ha hab)
    dsimp [R]
    nlinarith
  have hz := shiftedPrimeCutoff_bounds hX
  have hy : 1 < Real.exp (L/4) := Real.one_lt_exp_iff.mpr (by positivity)
  have hp := triplePrimeTuples_log_bound ha hab X (shiftedPrimeCutoff L)
    (Real.exp (L/4)) hy (tripleSieveCutoff_three hX) (tripleSieveCutoff_scale hX)
  have hcard : ((allPrimeTriples a b X).card:ℝ) ≤
      (triplePrimeTuples a b X (shiftedPrimeCutoff L)).card+shiftedPrimeCutoff L := by
    exact_mod_cast allPrimeTriples_cutoff ha (ha.trans hab) X (shiftedPrimeCutoff L)
  have hmain : 54*X*R/(Real.log (shiftedPrimeCutoff L))^3 ≤ 54*d^3*X*R/L^3 := by
    calc
      _ ≤ 54*X*R/(L/d)^3 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos (by positivity) 3) (pow_le_pow_left₀ (by positivity) hz.2.1 3)
      _ = _ := by field_simp
  have herr := tripleSieveCutoff_error hX
  rw [Real.exp_log hX0] at herr
  have herr' : 1152*(X:ℝ)/L^3 ≤ 1152*X*R/L^3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  calc
    _ ≤ 54*X*R/(Real.log (shiftedPrimeCutoff L))^3+
        (shiftedPrimeCutoff L+2*(Real.exp (L/4))^3) := by linarith
    _ ≤ 54*d^3*X*R/L^3+1152*X*R/L^3 := add_le_add hmain (herr.trans herr')
    _ = _ := by dsimp [L,d,R] <;> ring

 theorem uniform_prime_triple_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ,
    0 < a → a < b → ∀ X : ℕ, 2 ≤ X →
    ((allPrimeTriples a b X).card:ℝ) ≤ C*X*
      ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3 := by
  let K := 512*Real.log (4:ℝ)
  let A := 54*(256*Real.log (4:ℝ))^3+1152
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨A+K^3,by positivity,?_⟩
  intro a b ha hab X hX
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hR : 1 ≤ ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by
    have hh := totient_ratio_one_le (tripleDiscriminant_pos ha hab)
    nlinarith
  by_cases hlarge : K ≤ Real.log X
  · apply (allPrimeTriples_large_bound ha hab hlarge).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hpos : 0 ≤ (X:ℝ)*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by positivity
    nlinarith [mul_nonneg (pow_nonneg hK.le 3) hpos]
  · have hcard : ((allPrimeTriples a b X).card:ℝ) ≤ X := by exact_mod_cast allPrimeTriples_card_le a b X
    apply hcard.trans
    apply (le_div_iff₀ (pow_pos hL 3)).mpr
    have hpow := pow_le_pow_left₀ hL.le (le_of_not_ge hlarge) 3
    have h1 := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg X : (0:ℝ) ≤ X)
    have h2 := mul_le_mul_of_nonneg_left hR (show 0 ≤ (A+K^3)*X by positivity)
    nlinarith [mul_nonneg hA.le (Nat.cast_nonneg X : (0:ℝ) ≤ X)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeReciprocalTails
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal tails for the two and three linear prime forms in Ford's collision sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_triple_dyadic_count {C : ℝ}
    (hC : ∀ a b : ℕ,0 < a → a < b → ∀ X : ℕ,2 ≤ X →
      ((allPrimeTriples a b X).card:ℝ) ≤ C*X*
        ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q,q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      (C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log 2)^3)*
        (2:ℝ)^k/(k:ℝ)^3 := by
  have hsub : Q.filter (fun q => Nat.clog 2 q=k) ⊆ allPrimeTriples a b (2^k) := by
    intro q hq
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,hap,hbp⟩ := hQ q hq
    have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) q
    rw [he] at hpow
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le,hpow⟩,hp,hap,hbp⟩
  have hpow : 2 ≤ 2^k := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hh := hC a b ha hab (2^k) hpow
  push_cast at hh
  rw [Real.log_pow] at hh
  calc
    _ ≤ ((allPrimeTriples a b (2^k)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ C*(2:ℝ)^k*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/
      ((k:ℝ)*Real.log 2)^3 := hh
    _ = _ := by ring

theorem prime_triple_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (a b : ℕ),0 < a → a < b → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
      (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
      (∑ q ∈ Q,(q:ℝ)⁻¹) ≤
        C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log U)^2 := by
  obtain ⟨C,hC,hcount⟩ := uniform_prime_triple_bound
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨8*C/Real.log 2,by positivity,?_⟩
  intro a b ha hab Q U hU hQ
  have hh := finite_dyadic_log_cube_tail Q hU
    (show 0 ≤ C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/
      (Real.log 2)^3 by positivity)
    (fun q hq => (hQ q hq).1)
    (prime_triple_dyadic_count hcount ha hab Q (fun q hq => (hQ q hq).2))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionSieveTails
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height-uniform reciprocal sieve bounds for the two collision branches. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleDiscriminant_le_cube {a b : ℕ} {y : ℝ} (ha : (a:ℝ) ≤ y) (hb : (b:ℝ) ≤ y) :
    (tripleDiscriminant a b:ℝ) ≤ y^3 := by
  have hy : 0 ≤ y := (Nat.cast_nonneg a).trans ha
  have hsub : ((b-a:ℕ):ℝ) ≤ y := (by exact_mod_cast Nat.sub_le b a : ((b-a:ℕ):ℝ) ≤ b).trans hb
  dsimp [tripleDiscriminant]
  push_cast
  calc
    _ ≤ (y*y)*y := mul_le_mul
      (mul_le_mul ha hb (Nat.cast_nonneg _) hy) hsub (Nat.cast_nonneg _) (mul_nonneg hy hy)
    _ = _ := by ring

lemma B_cube {y : ℝ} (hy : Real.exp 2 ≤ y) : B (y^3)=Real.log 3+B y := by
  have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
  have hlog : 2 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  rw [B,Real.log_pow,Real.log_mul (by norm_num) (by linarith)]
  rfl

lemma cube_exp_two {y : ℝ} (hy : Real.exp 2 ≤ y) : Real.exp 2 ≤ y^3 := by
  have he := Real.add_one_le_exp (2:ℝ)
  have hy1 : 1 ≤ y := by linarith
  have hs : 1 ≤ y^2 := one_le_pow₀ hy1
  have hm := mul_le_mul_of_nonneg_left hs (zero_le_one.trans hy1)
  nlinarith

 theorem collision_triple_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (y : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → ∀ (a b : ℕ),0 < a → a < b →
    (a:ℝ) ≤ y → (b:ℝ) ≤ y → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
    (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log U)^2 := by
  obtain ⟨A,hA,htail⟩ := prime_triple_reciprocal_tail
  obtain ⟨R,hR,hratio⟩ := totient_ratio_loglog_bound
  let K := R*(1+Real.log (3:ℝ))
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨A*K^2,by positivity,?_⟩
  intro y hy hBy a b ha hab hay hby Q U hU hQ
  have hr := hratio (y^3) (cube_exp_two hy) (tripleDiscriminant a b)
    (tripleDiscriminant_pos ha hab) (tripleDiscriminant_le_cube hay hby)
  change (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ R*B (y^3) at hr
  rw [B_cube hy] at hr
  have hb : 0 ≤ B y := by linarith
  have hlog3 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hr' : (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient ≤ K*B y := by
    apply hr.trans
    have hh : Real.log 3+B y ≤ (1+Real.log 3)*B y := by nlinarith
    simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hh hR.le
  have hr0 : 0 ≤ (tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient := by positivity
  have hs := pow_le_pow_left₀ hr0 hr' 2
  calc
    _ ≤ A*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log U)^2 :=
      htail a b ha hab Q U hU hQ
    _ ≤ A*(K*B y)^2/(Real.log U)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hA.le) (sq_nonneg _)
    _ = _ := by ring

theorem collision_triple_reciprocal_tail_ne : ∃ C : ℝ,0 < C ∧
    ∀ (y : ℝ),Real.exp 2 ≤ y → 1 ≤ B y → ∀ (a b : ℕ),0 < a → 0 < b → a ≠ b →
    (a:ℝ) ≤ y → (b:ℝ) ≤ y → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
    (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log U)^2 := by
  obtain ⟨C,hC,hbound⟩ := collision_triple_reciprocal_tail
  refine ⟨C,hC,?_⟩
  intro y hy hB a b ha hb hab hay hby Q U hU hQ
  rcases lt_or_gt_of_ne hab with hlt|hgt
  · exact hbound y hy hB a b ha hlt hay hby Q U hU hQ
  · exact hbound y hy hB b a hb hgt hby hay Q U hU
      (fun q hq => ⟨(hQ q hq).1,(hQ q hq).2.1,(hQ q hq).2.2.2,(hQ q hq).2.2.1⟩)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquarefreeCollisionMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler-product bound for the squarefree interval factors in Ford's sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma squarefree_primeFactors_card {n : ℕ} (hn : Squarefree n) :
    n.primeFactors.card=n.primeFactorsList.length :=
  List.toFinset_card_of_nodup hn.nodup_primeFactorsList

lemma squarefree_reciprocal_moment (S Q : Finset ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S) :
    (∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) ≤
      Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) := by
  classical
  have hi : ∀ n ∈ Q,∀ m ∈ Q,n.primeFactors=m.primeFactors → n=m := by
    intro n hn m hm he
    rw [← Nat.prod_primeFactors_of_squarefree (hQ n hn).1,
      ← Nat.prod_primeFactors_of_squarefree (hQ m hm).1,he]
  have hsub : Q.image Nat.primeFactors ⊆ S.powerset := by
    intro T hT
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (hQ n hn).2
  have he (n : ℕ) (hn : n ∈ Q) : c^n.primeFactors.card/(n:ℝ)=
      ∏ p ∈ n.primeFactors,c/(p:ℝ) := by
    rw [Finset.prod_div_distrib,Finset.prod_const,← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hQ n hn).1]
  calc
    _ = ∑ n ∈ Q,∏ p ∈ n.primeFactors,c/(p:ℝ) := Finset.sum_congr rfl he
    _ = ∑ T ∈ Q.image Nat.primeFactors,∏ p ∈ T,c/(p:ℝ) :=
      by rw [Finset.sum_image hi]
    _ ≤ ∑ T ∈ S.powerset,∏ p ∈ T,c/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ =>
        Finset.prod_nonneg (fun p _ => div_nonneg hc (Nat.cast_nonneg p)))
    _ = ∏ p ∈ S,(1+c/(p:ℝ)) := by rw [← Finset.prod_one_add]
    _ ≤ ∏ p ∈ S,Real.exp (c/(p:ℝ)) := by
      apply Finset.prod_le_prod
      · intro p _
        positivity
      · intro p _
        have hh := Real.add_one_le_exp (c/(p:ℝ))
        linarith
    _ = _ := by
      rw [← Real.exp_sum,Finset.mul_sum]
      congr 1

/-- The elementary tilt giving Ford's `(e*i)^I` interval bound. -/
lemma squarefree_collision_mass (S Q : Finset ℕ) {c I H : ℝ} (hc : 1 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S ∧
      (n.primeFactors.card:ℝ) ≤ I)
    (hH : (∑ p ∈ S,(p:ℝ)⁻¹) ≤ H) (hIH : c*H ≤ I) :
    (∑ n ∈ Q,c^(2*n.primeFactors.card)/(n:ℝ)) ≤
      Real.exp (I*(Real.log c+1)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hmoment := squarefree_reciprocal_moment S Q hc0.le
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have ht : (∑ n ∈ Q,c^(2*n.primeFactors.card)/(n:ℝ)) ≤
      c^I*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hh := Real.rpow_le_rpow_of_exponent_le hc (hQ n hn).2.2
    rw [Real.rpow_natCast] at hh
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ c^n.primeFactors.card/(n:ℝ) by positivity)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    rw [two_mul,pow_add]
    ring
  calc
    _ ≤ c^I*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := ht
    _ ≤ c^I*Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hc0.le I)
    _ ≤ c^I*Real.exp I := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc0.le I)
      exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hH hc0.le).trans hIH)
    _ = _ := by
      rw [Real.rpow_def_of_pos hc0,← Real.exp_add]
      congr 1
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedFactorizations
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite encodings for ordered multiplicative factorizations. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prod_multiplyFactor {k : ℕ} (i : Fin k) (p : ℕ) (f : Fin k → ℕ) :
    (∏ j,multiplyFactor i p f j)=p*(∏ j,f j) := by
  have he := Finset.prod_update_of_mem (Finset.mem_univ i) f (f i)
  simp only [Function.update_eq_self] at he
  rw [multiplyFactor,Finset.prod_update_of_mem (Finset.mem_univ i),he]
  ring

lemma factorAllocations_card_le (k : ℕ) (L : List ℕ) :
    (factorAllocations k L).card ≤ k^L.length := by
  induction L with
  | nil => simp [factorAllocations]
  | cons p L ih =>
    calc
      _ ≤ ((Finset.univ : Finset (Fin k)) ×ˢ factorAllocations k L).card := Finset.card_image_le
      _ = k*(factorAllocations k L).card := by rw [Finset.card_product]; simp
      _ ≤ k*k^L.length := Nat.mul_le_mul_left k ih
      _ = _ := by simp [pow_succ,mul_comm]

lemma mem_factorAllocations {k : ℕ} (L : List ℕ)
    (hL : ∀ p ∈ L,p.Prime) (f : Fin k → ℕ) (hf : (∏ j,f j)=L.prod) :
    f ∈ factorAllocations k L := by
  induction L generalizing f with
  | nil =>
    have he : f=fun _ => 1 := by
      funext j
      apply Nat.eq_one_of_dvd_one
      simpa only [hf,List.prod_nil] using Finset.dvd_prod_of_mem f (Finset.mem_univ j)
    simp [factorAllocations,he]
  | cons p L ih =>
    have hp := hL p (List.mem_cons_self ..)
    have hd : p ∣ ∏ j,f j := by rw [hf,List.prod_cons]; exact dvd_mul_right p L.prod
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff f).mp hd
    let g := Function.update f i (f i/p)
    have he : multiplyFactor i p g=f := by
      funext j
      by_cases hj : j=i
      · subst j
        simp [multiplyFactor,g,Nat.mul_div_cancel' hi]
      · simp [multiplyFactor,g,hj]
    have hg : (∏ j,g j)=L.prod := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [← prod_multiplyFactor i p g,he,hf,List.prod_cons]
    apply Finset.mem_image.mpr
    exact ⟨(i,g),Finset.mem_product.mpr ⟨Finset.mem_univ _,
      ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) g hg⟩,he⟩

/-- Independent left and right allocations give the collision multiplicity. -/
theorem paired_factorizations_card_le (k n : ℕ) (hn : 0 < n)
    (Q : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hQ : ∀ f ∈ Q,(∏ j,f.1 j)=n ∧ (∏ j,f.2 j)=n) :
    Q.card ≤ k^(2*n.primeFactorsList.length) := by
  let A := factorAllocations k n.primeFactorsList
  have hsub : Q ⊆ A ×ˢ A := by
    intro f hf
    obtain ⟨hl,hr⟩ := hQ f hf
    apply Finset.mem_product.mpr
    constructor
    · apply mem_factorAllocations n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
      simpa only [Nat.prod_primeFactorsList hn.ne'] using hl
    · apply mem_factorAllocations n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
      simpa only [Nat.prod_primeFactorsList hn.ne'] using hr
  calc
    Q.card ≤ (A ×ˢ A).card := Finset.card_le_card hsub
    _ = A.card*A.card := Finset.card_product A A
    _ ≤ k^n.primeFactorsList.length*k^n.primeFactorsList.length :=
      Nat.mul_le_mul (factorAllocations_card_le k _) (factorAllocations_card_le k _)
    _ = _ := by rw [two_mul,pow_add]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RoughPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp reciprocal-prime mass and square-error bounds above a large cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_interval_reciprocal_eq {U V : ℝ} (hU : 2 ≤ U) (hUV : U ≤ V) :
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹)=
      primeReciprocalLE V-primeReciprocalLE U := by
  have hU0 : 0 ≤ U := by linarith
  have hV0 := hU0.trans hUV
  have hsub : primesUpTo U ⊆ primesUpTo V := by
    intro p hp
    obtain ⟨hp,hpU⟩ := (primesUpTo_mem hU0).mp hp
    exact (primesUpTo_mem hV0).mpr ⟨hp,hpU.trans hUV⟩
  have hsets : (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))=primesUpTo V \ primesUpTo U := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_sdiff,primesUpTo_mem hU0,primesUpTo_mem hV0]
    constructor
    · rintro ⟨⟨hp,hpV⟩,hUp⟩
      exact ⟨⟨hp,hpV⟩,fun h => (not_le_of_gt hUp) h.2⟩
    · rintro ⟨⟨hp,hpV⟩,hnot⟩
      exact ⟨⟨hp,hpV⟩,lt_of_not_ge (fun h => hnot ⟨hp,h⟩)⟩
  rw [hsets,Finset.sum_sdiff_eq_sub hsub]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PairedFactorizationMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted counts of actual ordered left and right interval factorizations. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma paired_factorization_mass_le (k : ℕ)
    (Q : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hQ : ∀ f ∈ Q,0 < (∏ j,f.1 j) ∧ (∏ j,f.1 j)=(∏ j,f.2 j)) :
    (∑ f ∈ Q,((∏ j,f.1 j):ℝ)⁻¹) ≤
      ∑ n ∈ Q.image (fun f => ∏ j,f.1 j),(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ) := by
  classical
  let F := fun f : (Fin k → ℕ) × (Fin k → ℕ) => ∏ j,f.1 j
  rw [← Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image.mpr ⟨f,hf,rfl⟩ :
    ∀ f ∈ Q,F f ∈ Q.image F)]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
  have hn0 := (hQ f hf).1
  let T := Q.filter (fun g => F g=F f)
  have hc := paired_factorizations_card_le k (F f) hn0 T (by
    intro g hg
    obtain ⟨hg,he⟩ := Finset.mem_filter.mp hg
    exact ⟨he,by rw [← (hQ g hg).2]; exact he⟩)
  have hcr : (T.card:ℝ) ≤ (k:ℝ)^(2*(F f).primeFactorsList.length) := by exact_mod_cast hc
  have he : (∑ g ∈ T,((F g):ℝ)⁻¹)=(T.card:ℝ)/(F f:ℝ) := by
    calc
      _ = ∑ _g ∈ T,(F f:ℝ)⁻¹ := Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2])
      _ = _ := by simp [div_eq_mul_inv]
  calc
    _ = (T.card:ℝ)/(F f:ℝ) := by simpa only [T,F,Nat.cast_prod] using he
    _ ≤ _ := div_le_div_of_nonneg_right hcr (Nat.cast_nonneg _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CommonPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal mass after one common largest prime has been extracted. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma common_prime_fiber_sum {k : ℕ} (E : Finset (PairedFactors k × ℕ))
    (r : PairedFactors k) :
    (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹)=
      (pairedProduct r:ℝ)⁻¹*
        (∑ q ∈ (E.filter (fun f => f.1=r)).image Prod.snd,(q:ℝ)⁻¹) := by
  classical
  rw [Finset.mul_sum,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    have he := (Finset.mem_filter.mp hf).2
    rw [he,Nat.cast_mul,mul_inv_rev]
    ring
  · intro f hf g hg he
    exact Prod.ext ((Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm) he

lemma common_prime_fiber_bound {k a b : ℕ} (i : Fin k) (y T C : ℝ)
    (htail : ∀ a b : ℕ,0 < a → 0 < b → a ≠ b → (a:ℝ) ≤ y → (b:ℝ) ≤ y →
      ∀ Q : Finset ℕ,(∀ q ∈ Q,T ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
        (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log T)^2)
    (E : Finset (PairedFactors k × ℕ))
    (hE : ∀ f ∈ E,CommonPrimeWitness a b i y T f)
    (r : PairedFactors k) (hr : r ∈ E.image Prod.fst) :
    (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*(pairedProduct r:ℝ)⁻¹ := by
  classical
  obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hr
  have hw := hE f hf
  have hlpos : 0 < a*r.1 i := by simpa only [he] using hw.left_pos
  have hrpos : 0 < b*r.2 i := by simpa only [he] using hw.right_pos
  have hlle : ((a*r.1 i:ℕ):ℝ) ≤ y := by simpa only [he] using hw.left_le
  have hrle : ((b*r.2 i:ℕ):ℝ) ≤ y := by simpa only [he] using hw.right_le
  have hne : a*r.1 i ≠ b*r.2 i := by
    intro h
    apply hw.different
    simp only [he,h]
  have ht := htail (a*r.1 i) (b*r.2 i) hlpos hrpos hne hlle hrle
    ((E.filter (fun f => f.1=r)).image Prod.snd) (by
      intro q hq
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hg,her⟩ := Finset.mem_filter.mp hg
      have hwg := hE g hg
      exact ⟨hwg.prime_lower,hwg.prime,by simpa only [her] using hwg.left_prime,
        by simpa only [her] using hwg.right_prime⟩)
  rw [common_prime_fiber_sum]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht
    (inv_nonneg.mpr (Nat.cast_nonneg (pairedProduct r)))

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RemovePrimeFactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one designated prime from a factorization and reconstructing it. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma multiply_divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : multiplyFactor i q (divideFactor i q f)=f := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [multiplyFactor,divideFactor,Nat.mul_div_cancel' hq]
  · simp [multiplyFactor,divideFactor,hj]

lemma prod_divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : q*(∏ j,divideFactor i q f j)=∏ j,f j := by
  rw [← prod_multiplyFactor,multiply_divideFactor i q f hq]

lemma divideFactor_prod_dvd {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : (∏ j,divideFactor i q f j) ∣ ∏ j,f j :=
  ⟨q,by rw [mul_comm,prod_divideFactor i q f hq]⟩

lemma divideFactor_prod_pos {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) : 0 < ∏ j,divideFactor i q f j := by
  have hh := prod_divideFactor i q f hq
  rw [← hh] at hf
  by_contra h
  have hz := Nat.eq_zero_of_not_pos h
  simp only [hz,mul_zero,lt_self_iff_false] at hf

lemma divideFactor_prod_omega_le {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) :
    (∏ j,divideFactor i q f j).primeFactorsList.length ≤ (∏ j,f j).primeFactorsList.length :=
  (Nat.primeFactorsList_sublist_of_dvd (divideFactor_prod_dvd i q f hq) hf.ne').length_le

lemma divideFactor_prod_factors {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) :
    (∏ j,divideFactor i q f j).primeFactorsList ⊆ (∏ j,f j).primeFactorsList :=
  Nat.primeFactorsList_subset_of_dvd (divideFactor_prod_dvd i q f hq) hf.ne'

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CommonLargestPrime
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recoverable extraction of the common largest prime from an actual pair of factors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma commonLargest_divisors {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    (largestPrimeFactor (f.1 i)).Prime ∧ largestPrimeFactor (f.1 i) ∣ f.1 i ∧
      largestPrimeFactor (f.1 i) ∣ f.2 i := by
  have hl := largestPrimeFactor_mem hf.left_two
  have hr := largestPrimeFactor_mem hf.right_two
  refine ⟨Nat.prime_of_mem_primeFactors hl,Nat.dvd_of_mem_primeFactors hl,?_⟩
  rw [hf.same_prime]
  exact Nat.dvd_of_mem_primeFactors hr

lemma commonLargest_decode {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    commonPrimeDecode i (commonLargestEncoding i f)=f := by
  obtain ⟨_,hl,hr⟩ := commonLargest_divisors hf
  exact Prod.ext (multiply_divideFactor i _ _ hl) (multiply_divideFactor i _ _ hr)

lemma commonLargest_product {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    pairedProduct (commonLargestEncoding i f).1*(commonLargestEncoding i f).2=pairedProduct f := by
  obtain ⟨_,hl,_⟩ := commonLargest_divisors hf
  change (∏ j,divideFactor i (largestPrimeFactor (f.1 i)) f.1 j)*largestPrimeFactor (f.1 i)=pairedProduct f
  rw [mul_comm,prod_divideFactor i _ _ hl]
  rfl

lemma commonLargest_witness {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (ha : 0 < a) (hb : 0 < b) (hf : CommonLargestConditions a b i y T U V I f) :
    CommonPrimeWitness a b i y T (commonLargestEncoding i f) := by
  obtain ⟨hq,hl,hr⟩ := commonLargest_divisors hf
  let q := largestPrimeFactor (f.1 i)
  have hl0 : 0 < f.1 i/q := Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0 < 2) hf.left_two) hl) hq.pos
  have hr0 : 0 < f.2 i/q := Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0 < 2) hf.right_two) hr) hq.pos
  have hele : a*(f.1 i/q) ≤ a*f.1 i := Nat.mul_le_mul_left a (Nat.div_le_self _ _)
  have here : b*(f.2 i/q) ≤ b*f.2 i := Nat.mul_le_mul_left b (Nat.div_le_self _ _)
  have heleR : ((a*(f.1 i/q):ℕ):ℝ) ≤ ((a*f.1 i:ℕ):ℝ) := by exact_mod_cast hele
  have hereR : ((b*(f.2 i/q):ℕ):ℝ) ≤ ((b*f.2 i:ℕ):ℝ) := by exact_mod_cast here
  have hel : a*(f.1 i/q)*q+1=a*f.1 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hl]
  have her : b*(f.2 i/q)*q+1=b*f.2 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hr]
  change CommonPrimeWitness a b i y T ((divideFactor i q f.1,divideFactor i q f.2),q)
  constructor
  · simpa [divideFactor] using Nat.mul_pos ha hl0
  · simpa [divideFactor] using Nat.mul_pos hb hr0
  · simpa [divideFactor] using heleR.trans hf.left_le
  · simpa [divideFactor] using hereR.trans hf.right_le
  · exact hf.prime_lower
  · exact hq
  · simpa only [divideFactor,Function.update_self,hel] using hf.left_prime
  · simpa only [divideFactor,Function.update_self,her] using hf.right_prime
  · simpa only [divideFactor,Function.update_self,hel,her] using hf.different

lemma commonLargest_residual {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    0 < pairedProduct (commonLargestEncoding i f).1 ∧
    pairedProduct (commonLargestEncoding i f).1=(∏ j,(commonLargestEncoding i f).1.2 j) ∧
    ((pairedProduct (commonLargestEncoding i f).1).primeFactorsList.length:ℝ) ≤ I ∧
    ∀ p ∈ (pairedProduct (commonLargestEncoding i f).1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
  obtain ⟨hq,hl,hr⟩ := commonLargest_divisors hf
  have he := prod_divideFactor i (largestPrimeFactor (f.1 i)) f.1 hl
  have he' := prod_divideFactor i (largestPrimeFactor (f.1 i)) f.2 hr
  refine ⟨divideFactor_prod_pos i _ _ hl hf.product_pos,?_,?_,?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hq.pos
    exact he.trans (hf.product_eq.trans he'.symm)
  · exact (show ((∏ j,divideFactor i (largestPrimeFactor (f.1 i)) f.1 j).primeFactorsList.length:ℝ) ≤
        (pairedProduct f).primeFactorsList.length by
      exact_mod_cast divideFactor_prod_omega_le i _ _ hl hf.product_pos).trans hf.omega_le
  · intro p hp
    exact hf.support p (divideFactor_prod_factors i _ _ hl hf.product_pos hp)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PairedSquarefreeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The application retains squarefreeness of the common band product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma paired_squarefree_allocation_bound (k : ℕ) (hk : 1 ≤ k)
    {U V I H : ℝ} (hU : 2 ≤ U) (hUV : U ≤ V)
    (hH : (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ H)
    (hI : (k:ℝ)*H ≤ I) (Q : Finset (PairedFactors k))
    (hQ : ∀ f ∈ Q,0 < pairedProduct f ∧ pairedProduct f=∏ j,f.2 j)
    (hsq : ∀ f ∈ Q,Squarefree (pairedProduct f))
    (hΩ : ∀ f ∈ Q,((pairedProduct f).primeFactorsList.length:ℝ) ≤ I)
    (hpf : ∀ f ∈ Q,∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) :
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
  classical
  let N := Q.image pairedProduct
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  have hV0 : 0 ≤ V := by linarith
  have hN (n : ℕ) (hn : n ∈ N) : Squarefree n ∧ n.primeFactors ⊆ S ∧ (n.primeFactors.card:ℝ) ≤ I := by
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    refine ⟨hsq f hf,?_,?_⟩
    · intro p hp
      have hp' : p ∈ (pairedProduct f).primeFactorsList := List.mem_toFinset.mp hp
      obtain ⟨hpU,hpV⟩ := hpf f hf p hp'
      exact Finset.mem_filter.mpr ⟨(primesUpTo_mem hV0).mpr
        ⟨Nat.prime_of_mem_primeFactorsList hp',hpV⟩,hpU⟩
    · rw [squarefree_primeFactors_card (hsq f hf)]
      exact hΩ f hf
  have hm := squarefree_collision_mass S N (by exact_mod_cast hk) hN hH hI
  have he : (∑ n ∈ N,(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ))=
      ∑ n ∈ N,(k:ℝ)^(2*n.primeFactors.card)/(n:ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [squarefree_primeFactors_card (hN n hn).1]
  have hc := paired_factorization_mass_le k Q hQ
  have himage : Q.image (fun f : PairedFactors k => ∏ j,f.1 j)=N := by
    ext n
    simp only [N,Finset.mem_image,pairedProduct]
  rw [himage] at hc
  have hc' : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      ∑ n ∈ N,(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ) := by
    simpa only [pairedProduct,Nat.cast_prod] using hc
  exact hc'.trans (he.trans_le hm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquarefreeIntervalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree interval estimate with an absolute Mertens error. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_interval_upper_bounded_error : ∃ D : ℝ,0 < D ∧ ∀ U V : ℝ,
    2 ≤ U → U ≤ V →
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ B V-B U+D := by
  obtain ⟨d,hd,hbound⟩ := primeReciprocalLE_bounded_error
  refine ⟨2*d,by positivity,?_⟩
  intro U V hU hUV
  have hu := hbound U hU
  have hv := hbound V (hU.trans hUV)
  rw [prime_interval_reciprocal_eq hU hUV]
  linarith [(abs_le.mp hu).1,(abs_le.mp hv).2]

/-- Unlike the general multiplicity bound, the application’s squarefree
product needs no relation between the number of slots and the lower cutoff. -/
theorem squarefree_interval_allocation_bound : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (U V I : ℝ),1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,0 < pairedProduct f ∧ pairedProduct f=∏ j,f.2 j) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∀ f ∈ Q,((pairedProduct f).primeFactorsList.length:ℝ) ≤ I) →
    (∀ f ∈ Q,∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
  obtain ⟨D,hD,hprime⟩ := prime_interval_upper_bounded_error
  exact ⟨D,hD,fun k U V I hk hU hUV hI Q hQ hsq hΩ hpf =>
    paired_squarefree_allocation_bound k hk hU hUV (hprime U V hU hUV) hI Q hQ hsq hΩ hpf⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CommonSquarefreeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-largest-prime bound for the globally squarefree application. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem common_prime_squarefree_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → 2 ≤ U →
    U ≤ V → (k:ℝ)*(B V-B U+D) ≤ I →
    ∀ E : Finset (PairedFactors k × ℕ),
    (∀ f ∈ E,CommonPrimeWitness a b i y T f) →
    (∀ f ∈ E,Squarefree (pairedProduct f.1)) →
    (∀ f ∈ E,0 < pairedProduct f.1 ∧ pairedProduct f.1=(∏ j,f.1.2 j) ∧
      ((pairedProduct f.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct f.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ E,((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,hC,htail⟩ := collision_triple_reciprocal_tail_ne
  obtain ⟨D,hD,halloc⟩ := squarefree_interval_allocation_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i y T U V I hy hBy hT hk hU hUV hI E hE hsq hQ
  let R := E.image Prod.fst
  let M := C*(B y)^2/(Real.log T)^2
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hmass : (∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
    have hR : ∀ r ∈ R,0 < pairedProduct r ∧ pairedProduct r=(∏ j,r.2 j) ∧
        ((pairedProduct r).primeFactorsList.length:ℝ) ≤ I ∧
        ∀ p ∈ (pairedProduct r).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
      intro r hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      exact hQ f hf
    apply halloc k U V I hk hU hUV hI R
    · exact fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩
    · intro r hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      exact hsq f hf
    · exact fun r hr => (hR r hr).2.2.1
    · exact fun r hr => (hR r hr).2.2.2
  have hmap : ∀ f ∈ E,f.1 ∈ R := fun f hf => Finset.mem_image.mpr ⟨f,hf,rfl⟩
  have hfiber (r : PairedFactors k) (hr : r ∈ R) :
      (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
        M*(pairedProduct r:ℝ)⁻¹ := by
    apply common_prime_fiber_bound i y T C _ E hE r hr
    intro a b ha hb hab hay hby Q hQ
    exact htail y hy hBy a b ha hb hab hay hby Q T hT hQ
  calc
    _ = ∑ r ∈ R,∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun f => ((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹)).symm
    _ ≤ ∑ r ∈ R,M*(pairedProduct r:ℝ)⁻¹ := Finset.sum_le_sum hfiber
    _ = M*(∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hM

/-- The equal-largest-prime branch, for the original finite family of pairs. -/
theorem common_largest_prime_squarefree_mass_bound_oai : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → 2 ≤ U →
    U ≤ V → (k:ℝ)*(B V-B U+D) ≤ I →
    ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,CommonLargestConditions a b i y T U V I f) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := common_prime_squarefree_mass_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i y T U V I ha hb hy hBy hT hk hU hUV hI Q hQ hsq
  let E := Q.image (commonLargestEncoding i)
  have hE : ∀ e ∈ E,CommonPrimeWitness a b i y T e := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_witness ha hb (hQ f hf)
  have hres : ∀ e ∈ E,0 < pairedProduct e.1 ∧ pairedProduct e.1=(∏ j,e.1.2 j) ∧
      ((pairedProduct e.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct e.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_residual (hQ f hf)
  have hi : ∀ f ∈ Q,∀ g ∈ Q,commonLargestEncoding i f=commonLargestEncoding i g → f=g := by
    intro f hf g hg he
    have hh := congrArg (commonPrimeDecode i) he
    rwa [commonLargest_decode (hQ f hf),commonLargest_decode (hQ g hg)] at hh
  have hsum : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹)=
      ∑ e ∈ E,((pairedProduct e.1*e.2:ℕ):ℝ)⁻¹ := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro f hf
    rw [commonLargest_product (hQ f hf)]
  rw [hsum]
  apply hbound k a b i y T U V I hy hBy hT hk hU hUV hI E hE _ hres
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact Squarefree.squarefree_of_dvd
    (divideFactor_prod_dvd i _ _ (commonLargest_divisors (hQ f hf)).2.1) (hsq f hf)

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.common_largest_prime_squarefree_mass_bound_oai := @OAI.TotientAsymptotic.common_largest_prime_squarefree_mass_bound_oai
