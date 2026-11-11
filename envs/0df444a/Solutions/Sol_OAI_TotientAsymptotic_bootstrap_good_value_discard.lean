-- Prove2me | solution 1 for OAI.TotientAsymptotic.bootstrap_good_value_discard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:38:27.156105+00:00
-- url     : https://prove2.me/submissions/1fcd66c5-cb47-4a07-abe8-c9b2dae2d46c

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
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
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_fordLemma26Input
import Theorems.Thm_OAI_TotientAsymptotic_two_coordinate_violation_count

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Basic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic data and renewal coefficients for counting totient values. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic



lemma isTotient_pos {d : ℕ} (hd : IsTotient d) : 0 < d := by
  obtain ⟨n, hn, rfl⟩ := hd
  exact Nat.totient_pos.mpr hn

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

lemma dyadic_endpoint_B (n : ℕ) :
    B ((2 : ℝ)^n)=Real.log ((n : ℝ)*Real.log 2) := by
  rw [B,dyadic_endpoint_log]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySmallParameter
attribute [-instance] _root_.instMeasurableSpace
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

lemma doubleLog_nat_pos {n : ℕ} (hn : 3 < n) : 0 < B n := by
  unfold B
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ)<n)).mpr
  have hn' : (3:ℝ) < n := by exact_mod_cast hn
  exact Real.exp_one_lt_three.trans hn'

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteDyadicHarmonic
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite reciprocal sum from dyadic counts of order y/log y. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma finite_dyadic_harmonic_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) (L : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hn : ∀ a ∈ Q, n a ∈ Finset.Icc 1 L)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(n a)/4 ≤ v a)
    (hcount : ∀ k ∈ Finset.Icc 1 L, ((Q.filter (fun a => n a=k)).card : ℝ) ≤
      A*(2 : ℝ)^k/(k : ℝ)) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ 4*A*(1+Real.log L) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (k : ℕ) (hk : k ∈ Finset.Icc 1 L) :
      (∑ a ∈ Q.filter (fun a => n a=k), (v a)⁻¹) ≤ 4*A*(k : ℝ)⁻¹ := by
    have hy : (0 : ℝ) < (2 : ℝ)^k := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => n a=k), 4/(2 : ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
        have hh := hlo a ha
        rw [he] at hh
        have hr := inv_anti₀ (div_pos hy (by norm_num)) hh
        simpa only [inv_div] using hr
      _ = ((Q.filter (fun a => n a=k)).card : ℝ)*(4/(2 : ℝ)^k) := by simp
      _ ≤ (A*(2 : ℝ)^k/(k : ℝ))*(4/(2 : ℝ)^k) :=
        mul_le_mul_of_nonneg_right (hcount k hk) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 L, 4*A*(k : ℝ)⁻¹ := Finset.sum_le_sum hf
    _ = 4*A*(harmonic L : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derive the exceptional reciprocal-prime mass from Ford's count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonNormalPrime_ge_three {S : ℝ} {N p : ℕ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hp : p ∈ nonNormalPrimes S N) : 3 ≤ p := by
  obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  by_contra hh
  have he : p=2 := by have := hprime.two_le; omega
  subst p
  exact hn (normal_two hS hBS)

lemma dyadic_shift_lower {p : ℕ} (hp : 2 ≤ p) :
    (2 : ℝ)^(Nat.clog 2 p)/4 ≤ ((p-1 : ℕ) : ℝ) := by
  have hd := (dyadic_nat_bounds (by omega : 1 < p)).2.1
  have hsub : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast (show p-1+1=p by omega)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- The only arithmetic input is the literal count in Ford Lemma 2.6.
Dyadic summation supplies its needed reciprocal-weight consequence. -/
theorem non_normal_prime_mass (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → 0 ≤ B S → ∀ N : ℕ, 4 ≤ N →
      let L := Nat.clog 2 N
      (∑ p ∈ nonNormalPrimes S N, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        C*(B ((2 : ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6 : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := hford
  refine ⟨4*C/Real.log 2,by positivity,?_⟩
  intro S hS hBS N hN
  dsimp only
  let L := Nat.clog 2 N
  let Q := nonNormalPrimes S N
  let W := B ((2 : ℝ)^L)
  let E := (Real.log S)^(-1/6 : ℝ)
  let A := C*W^5*E/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 2 ≤ L := by
    have hh := Nat.clog_mono_right 2 hN
    have hc : Nat.clog 2 4=2 := by
      exact Nat.clog_pow 2 2 (by norm_num)
    rw [hc] at hh
    exact hh
  have hW : 0 ≤ W := by
    dsimp [W]
    rw [dyadic_endpoint_B]
    apply Real.log_nonneg
    have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [Real.log_two_gt_d9]
  have hE : 0 ≤ E := Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ S)) _
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg hC.le (pow_nonneg hW _)) hE) hlog2.le
  have hn : ∀ p ∈ Q, Nat.clog 2 p ∈ Finset.Icc 1 L := by
    intro p hp
    have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
    refine Finset.mem_Icc.mpr ⟨(dyadic_nat_bounds (by omega : 1 < p)).1,?_⟩
    exact Nat.clog_mono_right 2 ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1)
  have hf : ∀ k ∈ Finset.Icc 1 L,
      ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤ A*(2 : ℝ)^k/(k : ℝ) := by
    intro k hk
    by_cases hne : (Q.filter (fun p => Nat.clog 2 p=k)).Nonempty
    · obtain ⟨p,hp⟩ := hne
      obtain ⟨hp,hpk⟩ := Finset.mem_filter.mp hp
      have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
      have hk2 : 2 ≤ k := by
        have he : 1 < Nat.clog 2 p := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
        omega
      have hsub : Q.filter (fun p => Nat.clog 2 p=k) ⊆ nonNormalPrimes S (2^k) := by
        intro p hp
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hnormal⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_,(Nat.mem_primesLE.mp hp).2⟩,hnormal⟩
        simpa only [he] using Nat.le_pow_clog (by norm_num : 1 < 2) p
      have hklarge : 3 < (2 : ℕ)^k := by
        have he := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2
        norm_num at he ⊢
        omega
      have hb := (show ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          (nonNormalPrimes S (2^k)).card by exact_mod_cast Finset.card_le_card hsub).trans
        (hcount S hS (2^k) hklarge)
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hWk : 0 ≤ B ((2 : ℝ)^k) := by
        rw [dyadic_endpoint_B]
        apply Real.log_nonneg
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith [Real.log_two_gt_d9]
      have hWB : B ((2 : ℝ)^k) ≤ W := by
        dsimp [W]
        rw [dyadic_endpoint_B,dyadic_endpoint_B]
        apply Real.log_le_log (mul_pos hkpos hlog2)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hlog2.le
      have hb' : ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*(B ((2 : ℝ)^k))^5*E := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat,E] using hb
      apply hb'.trans
      calc
        _ ≤ C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*W^5*E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hWk hWB 5) (by rw [dyadic_endpoint_log]; positivity)) hE
        _ = _ := by dsimp [A]; rw [dyadic_endpoint_log]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      positivity
  have he := finite_dyadic_harmonic_mass Q (Nat.clog 2)
    (fun p => ((p-1 : ℕ) : ℝ)) L hA hn
    (fun p hp => dyadic_shift_lower (by have := nonNormalPrime_ge_three (by linarith) hBS hp; omega)) hf
  apply he.trans_eq
  dsimp [A,W,E,L]
  ring

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct totient values after adjoining a large prime to a residual preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma mem_quarterPrimes {x : ℝ} {d p : ℕ} (hd : 0 < d) :
    p ∈ quarterPrimes x d ↔ p.Prime ∧ x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x := by
  classical
  constructor
  · intro hp
    obtain ⟨hp,hx,hs⟩ := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2,hx,hs⟩
  · rintro ⟨hp,hx,hs⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_,hp⟩,hx,hs⟩
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hpn : 1 ≤ p := hp.one_le
    have hle : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hs
    have hh := (le_div_iff₀ hdR).mpr hle
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCoverage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coverage of large-prime totients by their residual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma totient_prime_extension_cases {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    n.totient=(p-1)*(n/p).totient ∨ n.totient=p*(n/p).totient := by
  have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
  by_cases hd : p ∣ n/p
  · right
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_dvd hp hd
  · left
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_not_dvd hp hd

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NonNormalExtensionCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual-value grouping for the large-prime half of Ford Lemma 2.8. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

/-- On a nonempty prime interval, its lower cutoff supplies the logarithm
in Ford's exceptional-prime estimate. -/
theorem non_normal_quarter_prime_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ d : ℕ,0 < d → ∀ Q : Finset ℕ,
    (∀ p ∈ Q,p.Prime ∧ 4 ≤ p ∧ x^(1/4:ℝ) ≤ p ∧
      ((p-1)*d:ℕ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hford⟩ := fordLemma26Input
  refine ⟨8*C,by positivity,?_⟩
  intro S x hS hx d hd Q hQ
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlS : 0 < Real.log S := Real.log_pos (by linarith)
  have hs : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlS.le _
  by_cases hne : Q.Nonempty
  · let N := ⌊1+x/d⌋₊
    have hpN (p : ℕ) (hp : p ∈ Q) : p ≤ N := by
      have hh := (hQ p hp).2.2.2.1
      have hp1 : 1 ≤ p := (hQ p hp).1.one_le
      have hhR : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hh
      apply Nat.le_floor
      have hdiv := (le_div_iff₀ hd0).mpr hhR
      linarith
    obtain ⟨p,hp⟩ := hne
    have hN4 : 4 ≤ N := (hQ p hp).2.1.trans (hpN p hp)
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlogN : Real.log x/4 ≤ Real.log N := by
      have hlo := (hQ p hp).2.2.1.trans (Nat.cast_le.mpr (hpN p hp))
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlo
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogN0 : 0 < Real.log N := Real.log_pos hN1
    have hdx : (d:ℝ) ≤ x := by
      have hp1 : 1 ≤ p-1 := by have := (hQ p hp).1.two_le; omega
      exact (Nat.cast_le.mpr (show d ≤ (p-1)*d by nlinarith)).trans (hQ p hp).2.2.2.1
    have hNupper : (N:ℝ) ≤ 2*x/d := by
      have hn : (N:ℝ) ≤ 1+x/d := Nat.floor_le (by positivity)
      have hh : (1:ℝ) ≤ x/d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
      rw [show 2*x/(d:ℝ)=2*(x/d) by ring]
      linarith only [hn,hh]
    have hN2x : (N:ℝ) ≤ 2*x := hNupper.trans ((div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0]))
    have hBN : 0 ≤ B N := (doubleLog_nat_pos hN4).le
    have hBmono : B N ≤ B (2*x) := by
      apply Real.log_le_log hlogN0
      exact Real.log_le_log hN0 hN2x
    have hB2 : 0 ≤ B (2*x) := hBN.trans hBmono
    have hsub : Q ⊆ nonNormalPrimes S N := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN q hq,(hQ q hq).1⟩,(hQ q hq).2.2.2.2⟩
    have hcard : (Q.card:ℝ) ≤ (nonNormalPrimes S N).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hrat : C*N/Real.log N ≤ 8*C*x/(d*Real.log x) := by
      calc
        _ ≤ C*(2*x/d)/(Real.log x/4) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hNupper hC.le)
            (by positivity) hlogN
        _ = _ := by ring
    calc
      _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) :=
        hcard.trans (hford S hS N hN4)
      _ ≤ (8*C*x/(d*Real.log x))*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hs
        exact mul_le_mul hrat (pow_le_pow_left₀ hBN hBmono 5) (by positivity) (by positivity)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hB2 : 0 ≤ B (2*x) := by
      have hh : B 4 ≤ B (2*x) := Real.log_le_log
        (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
      exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientCountingEnvelope
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic counting envelope used to bootstrap the global upper bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadicTotientEnvelope_one_le (J : ℕ) : 1 ≤ dyadicTotientEnvelope J := le_max_left _ _

lemma dyadicTotientEnvelope_term_le {k J : ℕ} (hkJ : k ≤ J) :
    V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k ≤ dyadicTotientEnvelope J := by
  unfold dyadicTotientEnvelope
  have hs : k ∈ Finset.range (J+1) := Finset.mem_range.mpr (by omega)
  exact (Finset.le_sup' (s:=Finset.range (J+1))
    (fun k => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k) hs).trans (le_max_right _ _)

lemma dyadic_totient_count_le {k J : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    V ((2:ℝ)^k) ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpow : (0:ℝ) < 2^k := by positivity
  have he := dyadicTotientEnvelope_term_le hkJ
  apply (le_div_iff₀ hk0).mpr
  exact (div_le_iff₀ hpow).mp he

lemma totient_values_subset {x y : ℝ} (hxy : x ≤ y) : totientValues x ⊆ totientValues y := by
  classical
  intro v hv
  obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hv).1,(Finset.mem_Icc.mp hv).2.trans (Nat.floor_mono hxy)⟩,ht⟩

lemma V_monotone : Monotone V := by
  intro x y hxy
  exact Nat.cast_le.mpr (Finset.card_le_card (totient_values_subset hxy))

lemma dyadic_totient_reciprocal_mass {J : ℕ} (_hJ : 1 ≤ J) (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ (2:ℝ)^J) :
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+4*dyadicTotientEnvelope J*(1+Real.log J) := by
  classical
  let E := Q.erase 1
  have hE (v : ℕ) (hv : v ∈ E) : IsTotient v ∧ 1 < v ∧ (v:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    have h := hQ v hv
    exact ⟨h.1,by have := isTotient_pos h.1; omega,h.2⟩
  have hn : ∀ v ∈ E,Nat.clog 2 v ∈ Finset.Icc 1 J := by
    intro v hv
    have hb := dyadic_nat_bounds (hE v hv).2.1
    refine Finset.mem_Icc.mpr ⟨hb.1,?_⟩
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    exact_mod_cast (hE v hv).2.2
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 J) :
      ((E.filter (fun v => Nat.clog 2 v=k)).card:ℝ) ≤
      dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
    have hsub : E.filter (fun v => Nat.clog 2 v=k) ⊆ totientValues ((2:ℝ)^k) := by
      intro v hv
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have h := hE v hv
      have hb := (dyadic_nat_bounds h.2.1).2.2
      rw [he] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨isTotient_pos h.1,Nat.le_floor hb⟩,h.1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (dyadic_totient_count_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  have hm := finite_dyadic_harmonic_mass E (Nat.clog 2) (fun v => (v:ℝ)) J
    (zero_le_one.trans (dyadicTotientEnvelope_one_le J)) hn (by
      intro v hv
      have hh := (dyadic_nat_bounds (hE v hv).2.1).2.1
      have hp : (0:ℝ) < 2^(Nat.clog 2 v) := by positivity
      linarith) hcount
  have hs : (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+∑ v ∈ E,(v:ℝ)⁻¹ := by
    by_cases h1 : 1 ∈ Q
    · rw [← Finset.add_sum_erase Q _ h1]
      norm_num [E]
    · have he : E=Q := Finset.erase_eq_of_notMem h1
      rw [he]
      linarith
  exact hs.trans (add_le_add le_rfl hm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeNonNormalValues
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct exceptional totient values, grouped by the residual value. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma abnormal_extension_values_card (S x : ℝ) (d : ℕ) :
    (abnormalExtensionValues S x d).card ≤ 2*(abnormalExtensionPrimes S x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ abnormalExtensionPrimes S x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

lemma totient_mem_abnormalExtensionValues {S x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hp4 : 4 ≤ p)
    (hpx : x^(1/4:ℝ) ≤ p) (hx : (n.totient:ℝ) ≤ x) (hbad : ¬IsNormalPrime S p) :
    n.totient ∈ abnormalExtensionValues S x (n/p).totient := by
  classical
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
    (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases totient_prime_extension_cases hp hpn with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr
    ⟨(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,hp4,hbad⟩,?_⟩
  rcases totient_prime_extension_cases hp hpn with h|h <;>
    simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- Large non-normal prime divisors cost only the reciprocal mass of the
residual totient values, even when a value has many preimages. -/
theorem large_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧ 4 ≤ p ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      ∑ d ∈ R,(d:ℝ)⁻¹ := by
  classical
  obtain ⟨C,hC,hcount⟩ := non_normal_quarter_prime_count
  refine ⟨2*C,by positivity,?_⟩
  intro S x hS hx R Q hR hQ
  have hsub : Q ⊆ R.biUnion (abnormalExtensionValues S x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hp4,hpx,hvx,hbad,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← hφ]
    exact totient_mem_abnormalExtensionValues hn hp hpn hp4 hpx (by rwa [hφ]) hbad
  have hbound (d : ℕ) (hd : d ∈ R) :
      ((abnormalExtensionValues S x d).card:ℝ) ≤
      (2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ := by
    have hh := hcount S x hS hx d (hR d hd) (abnormalExtensionPrimes S x d) (by
      intro p hp
      obtain ⟨hp,hp4,hbad⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hpx,hsize⟩ := (mem_quarterPrimes (hR d hd)).mp hp
      exact ⟨hp,hp4,hpx,hsize,hbad⟩)
    have hc : ((abnormalExtensionValues S x d).card:ℝ) ≤
        2*((abnormalExtensionPrimes S x d).card:ℝ) := by
      exact_mod_cast abnormal_extension_values_card S x d
    calc
      _ ≤ 2*((abnormalExtensionPrimes S x d).card:ℝ) := hc
      _ ≤ 2*(C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ((R.biUnion (abnormalExtensionValues S x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ R,((abnormalExtensionValues S x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (abnormalExtensionValues S x)).card ≤
        ∑ d ∈ R,(abnormalExtensionValues S x d).card)
    _ ≤ ∑ d ∈ R,(2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ :=
      Finset.sum_le_sum hbound
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicValueBounds
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise value-counting bounds from the finite dyadic envelope. -/
noncomputable section
namespace TotientAsymptotic

lemma dyadic_value_count_bound {N J : ℕ} (hN : 2 ≤ N) (hNJ : N ≤ 2^J) :
    V N ≤ 2*dyadicTotientEnvelope J*N/Real.log N := by
  let k := Nat.clog 2 N
  have hb := dyadic_nat_bounds (by omega : 1 < N)
  have hk : 1 ≤ k := hb.1
  have hkJ : k ≤ J := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hNJ
  have hNpow : (N:ℝ) ≤ (2:ℝ)^k := hb.2.2
  have hpowN : (2:ℝ)^k ≤ 2*N := by linarith [hb.2.1]
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log N ≤ k := by
    have hh := Real.log_le_log hN0 hNpow
    rw [Real.log_pow] at hh
    have hl2 : Real.log (2:ℝ) ≤ 1 := by
      have he := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at he
      exact he
    have hm := mul_le_mul_of_nonneg_left hl2 hk0.le
    nlinarith only [hh,hm]
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ V ((2:ℝ)^k) := V_monotone hNpow
    _ ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := dyadic_totient_count_le hk hkJ
    _ ≤ 2*dyadicTotientEnvelope J*N/(k:ℝ) := by
      apply div_le_div_of_nonneg_right _ hk0.le
      nlinarith only [mul_le_mul_of_nonneg_left hpowN hE]
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hlN hlog

lemma log_floor_lower {x : ℝ} (hx : 4 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ Real.log x/2 ≤ Real.log (⌊x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hN : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by norm_num <;> linarith)
  refine ⟨hN,?_⟩
  have hh : x/2 ≤ (⌊x⌋₊:ℝ) := by linarith [Nat.sub_one_lt_floor x]
  have hl := Real.log_le_log (by positivity : 0 < x/2) hh
  rw [Real.log_div (by linarith : x ≠ 0) (by norm_num)] at hl
  have hl4 : Real.log (4:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [he] at hl4
  linarith

lemma V_floor (x : ℝ) : V (⌊x⌋₊:ℝ)=V x := by
  unfold V
  rw [Nat.floor_natCast]

lemma dyadic_real_value_count_bound {x : ℝ} {J : ℕ} (hx : 4 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) : V x ≤ 4*dyadicTotientEnvelope J*x/Real.log x := by
  have hfloor := log_floor_lower hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hfloorlog : 0 < Real.log (⌊x⌋₊:ℝ) := lt_of_lt_of_le (by positivity) hfloor.2
  have hN : ⌊x⌋₊ ≤ 2^J := by
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ x)).trans hJ
  have hb := dyadic_value_count_bound hfloor.1 hN
  rw [V_floor] at hb
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ 2*dyadicTotientEnvelope J*(⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ) := hb
    _ ≤ 2*dyadicTotientEnvelope J*x/Real.log (⌊x⌋₊:ℝ) := by
      apply div_le_div_of_nonneg_right _ hfloorlog.le
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by positivity)
    _ ≤ 2*dyadicTotientEnvelope J*x/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfloor.2
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDivisorValueCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact value counting by a selected prime divisor of a preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma totient_mem_divisorExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ divisorExtensionValues x p := by
  classical
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  have hp1 : (0:ℝ) < (p-1:ℕ) := by exact_mod_cast (show 0 < p-1 by have := hp.two_le; omega)
  have hdsize : ((n/p).totient:ℝ) ≤ x/(p-1:ℕ) := by
    apply (le_div_iff₀ hp1).mpr
    simpa only [Nat.cast_mul,mul_comm] using hsize
  have hdmem : (n/p).totient ∈ totientValues (x/(p-1:ℕ)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdsize⟩,⟨n/p,hq,rfl⟩⟩
  rcases hcases with h|h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)

lemma divisorExtensionValues_card (x : ℝ) (p : ℕ) :
    ((divisorExtensionValues x p).card:ℝ) ≤ 2*V (x/(p-1:ℕ)) := by
  classical
  have hh : (divisorExtensionValues x p).card ≤
      (totientValues (x/(p-1:ℕ))).card+(totientValues (x/(p-1:ℕ))).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
  change ((divisorExtensionValues x p).card:ℝ) ≤ 2*((totientValues (x/(p-1:ℕ))).card:ℝ)
  have hhR : ((divisorExtensionValues x p).card:ℝ) ≤
      ((totientValues (x/(p-1:ℕ))).card:ℝ)+(totientValues (x/(p-1:ℕ))).card := by
    exact_mod_cast hh
  linarith

theorem prime_divisor_value_count (x : ℝ) (P Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := by
  classical
  have hs : Q ⊆ P.biUnion (divisorExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hP⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨p,hP,?_⟩
    rw [← hφ]
    exact totient_mem_divisorExtensionValues hn hp hpn (by rwa [hφ])
  calc
    _ ≤ ((P.biUnion (divisorExtensionValues x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hs)
    _ ≤ ∑ p ∈ P,((divisorExtensionValues x p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion (divisorExtensionValues x)).card ≤
        ∑ p ∈ P,(divisorExtensionValues x p).card)
    _ ≤ ∑ p ∈ P,2*V (x/(p-1:ℕ)) := Finset.sum_le_sum (fun p _ => divisorExtensionValues_card x p)
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallPrimeValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-prime half of the exceptional-value count in Ford Lemma 2.8.
The envelope counts residual totient values, independently of fiber sizes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma small_divisor_value_bound {x : ℝ} {d J : ℕ} (hx : 16 ≤ x)
    (hd : 0 < d) (hdx : (d:ℝ)^2 ≤ x) (hJ : x ≤ (2:ℝ)^J) :
    V (x/d) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*(d:ℝ)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdx' : (d:ℝ) ≤ x/4 := by
    by_contra hh
    have hh' : x/4 < (d:ℝ) := lt_of_not_ge hh
    have hd4 : 4 < (d:ℝ) := by linarith
    nlinarith only [hdx,hh',hd4]
  have ht4 : 4 ≤ x/d := (le_div_iff₀ hd0).mpr (by linarith)
  have htx : x/d ≤ x := (div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0])
  have hlog : Real.log x/2 ≤ Real.log (x/d) := by
    have hh := Real.log_le_log (sq_pos_of_pos hd0) hdx
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [Real.log_div hx0.ne' hd0.ne']
    linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  have hb := dyadic_real_value_count_bound ht4 (htx.trans hJ)
  calc
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/Real.log (x/d) := hb
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
    _ = _ := by ring

/-- Prime divisors up to the square-root scale, with no choice of preimage
counted more than once. -/
theorem small_prime_value_count {x : ℝ} {J : ℕ} (hx : 16 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime ∧ (p:ℝ)^2 ≤ x)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
      ∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹ := by
  have hb := prime_divisor_value_count x P Q hQ
  have hpbound (p : ℕ) (hp : p ∈ P) :
      V (x/(p-1:ℕ)) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ := by
    have hprime := (hP p hp).1
    apply small_divisor_value_bound hx (by have := hprime.two_le; omega) _ hJ
    have hs : ((p-1:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2).trans (hP p hp).2
  calc
    _ ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := hb
    _ ≤ 2*∑ p ∈ P,(8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpbound) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exceptional-value bound for small prime factors. -/
theorem small_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
        (Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hmass⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨16*C,by positivity,?_⟩
  intro S x N J hS hBS hN hx hNx hJ Q hQ
  have hP (p : ℕ) (hp : p ∈ nonNormalPrimes S N) : p.Prime ∧ (p:ℝ)^2 ≤ x := by
    have hh := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact ⟨hh.2,(pow_le_pow_left₀ (Nat.cast_nonneg p) (by exact_mod_cast hh.1) 2).trans hNx⟩
  have hb := small_prime_value_count hx hJ (nonNormalPrimes S N) Q hP (by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hv,hle,hnormal⟩ := hQ v hv
    exact ⟨n,p,hn,hφ,hp,hpn,hv,Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩,hnormal⟩⟩)
  have hc : 0 ≤ 16*dyadicTotientEnvelope J*x/Real.log x := by
    have := Real.log_pos (show 1 < x by linarith)
    have := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
    positivity
  calc
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        ∑ p ∈ nonNormalPrimes S N,((p-1:ℕ):ℝ)⁻¹ := hb
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        (C*(B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass S hS hBS N hN) hc
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExceptionalValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete non-normal-prime contribution to Ford's nice-value exception.
All fibers are handled by finite value covers, without multiplicity weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma totient_div_prime_le {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (n/p).totient ≤ n.totient := by
  have hp1 : 1 ≤ p-1 := by have := hp.two_le; omega
  rcases totient_prime_extension_cases hp hpn with h|h
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp1
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp.one_le

/-- A finite, uniform form of the non-normal-prime part of Ford Lemma 2.8.
The two numeric inequalities select any cutoff between the fourth-root and
square-root scales. -/
theorem non_normal_value_count_split : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x^(1/4:ℝ) ≤ N → 1 ≤ J → x ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
          (Real.log S)^(-1/6:ℝ) +
      (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
        (1+4*dyadicTotientEnvelope J*(1+Real.log J)) := by
  obtain ⟨C,hC,hsmall⟩ := small_non_normal_value_count
  obtain ⟨D,hD,hlarge⟩ := large_non_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S x N J hS hBS hN hx hNx hroot hJ hxJ Q hQ
  let A := Q.filter (fun v => ∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
    (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p)
  let T := Q\A
  have hsmall' := hsmall S x N J hS hBS hN hx hNx hxJ A
    (fun v hv => (Finset.mem_filter.mp hv).2)
  have hres (d : ℕ) (hd : d ∈ totientValues x) :
      IsTotient d ∧ (d:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hd,ht⟩ := Finset.mem_filter.mp hd
    exact ⟨ht,(Nat.floor_le (by linarith : 0 ≤ x)).trans' (Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2) |>.trans hxJ⟩
  have hlarge' := hlarge S x hS (by linarith) (totientValues x) T
    (fun d hd => isTotient_pos (hres d hd).1) (by
      intro v hv
      obtain ⟨hvQ,hvA⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hbad⟩ := hQ v hvQ
      have hpN : N < p := by
        by_contra hh
        exact hvA (Finset.mem_filter.mpr ⟨hvQ,n,p,hn,hφ,hp,hpn,hvx,by omega,hbad⟩)
      have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
        (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
      have hdx : ((n/p).totient:ℝ) ≤ x :=
        (Nat.cast_le.mpr (totient_div_prime_le hp hpn)).trans (by rwa [hφ])
      refine ⟨n,p,hn,hφ,hp,hpn,by omega,hroot.trans (by exact_mod_cast hpN.le),hvx,hbad,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdx⟩,⟨n/p,
        Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos,rfl⟩⟩)
  have hB : 0 ≤ B (2*x) := by
    have hh : B 4 ≤ B (2*x) := Real.log_le_log
      (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
    exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
  have hcoef : 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
    have := Real.log_pos (show 1 < x by linarith)
    have := Real.log_pos (show 1 < S by linarith)
    positivity
  have hmass := dyadic_totient_reciprocal_mass hJ (totientValues x) hres
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(T.card:ℝ) := by
    have hsubset : A ⊆ Q := Finset.filter_subset _ _
    have hh := Finset.card_sdiff_add_card_eq_card hsubset
    dsimp only [T]
    exact_mod_cast (show Q.card=A.card+(Q\A).card by omega)
  rw [hcard]
  exact add_le_add hsmall' (hlarge'.trans (mul_le_mul_of_nonneg_left hmass hcoef))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeavyOmegaMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed 15/8 moment needed for the large-Omega nice-value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma heavyOmegaReciprocal_nonneg (n : ℕ) : 0 ≤ heavyOmegaReciprocal n := by
  change 0 ≤ (15/8:ℝ)^n.primeFactorsList.length/(n:ℝ)
  positivity

lemma heavyOmegaReciprocal_prime {p : ℕ} (hp : p.Prime) :
    heavyOmegaReciprocal p=(15/8:ℝ)/p := by
  simp [heavyOmegaReciprocal,Nat.primeFactorsList_prime hp]

lemma heavyOmegaReciprocal_norm {p : ℕ} (hp : p.Prime) :
    ‖heavyOmegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (heavyOmegaReciprocal_nonneg p),heavyOmegaReciprocal_prime hp]
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma heavy_omega_euler_log {p : ℕ} (hp : p.Prime) :
    Real.log ((1-heavyOmegaReciprocal p)⁻¹) ≤ (15/8:ℝ)/p+64/(p:ℝ)^2 := by
  rw [heavyOmegaReciprocal_prime hp]
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hx0 : 0 ≤ (15/8:ℝ)/p := by positivity
  have hx : (15/8:ℝ)/p ≤ 15/16 := (div_le_iff₀ hp0).mpr (by linarith)
  have hTaylor := Real.abs_log_sub_add_sum_range_le
    (show |(15/8:ℝ)/p| < 1 by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    zero_add,pow_one,div_one,abs_of_nonneg hx0] at hTaylor
  have hquad : ((15/8:ℝ)/p)^2/(1-(15/8:ℝ)/p) ≤ 64/(p:ℝ)^2 := by
    have hden : (1/16:ℝ) ≤ 1-(15/8:ℝ)/p := by linarith
    calc
      _ ≤ ((15/8:ℝ)/p)^2/(1/16) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
      _ = (225/4:ℝ)/(p:ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  rw [Real.log_inv]
  linarith [(abs_le.mp hTaylor).1]

lemma heavy_omega_euler_product (N : ℕ) :
    (∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(1-heavyOmegaReciprocal p)⁻¹) ≤
      Real.exp ((15/8:ℝ)*primeReciprocalLE N+64) := by
  classical
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < (1-heavyOmegaReciprocal p)⁻¹ := by
    have hh := heavyOmegaReciprocal_norm (Finset.mem_filter.mp hp).2
    rw [Real.norm_eq_abs,abs_of_nonneg (heavyOmegaReciprocal_nonneg p)] at hh
    exact inv_pos.mpr (by linarith)
  apply (Real.log_le_iff_le_exp (Finset.prod_pos hpos)).mp
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  calc
    _ ≤ ∑ p ∈ P,((15/8:ℝ)/p+64/(p:ℝ)^2) :=
      Finset.sum_le_sum (fun p hp => heavy_omega_euler_log (Finset.mem_filter.mp hp).2)
    _ = (15/8:ℝ)*(∑ p ∈ P,(p:ℝ)⁻¹)+64*(∑ p ∈ P,1/(p:ℝ)^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (15/8:ℝ)*primeReciprocalLE N+64 := by
      have he : (∑ p ∈ P,(p:ℝ)⁻¹)=primeReciprocalLE N := by
        simp only [P,primeReciprocalLE,primesUpTo,Nat.floor_natCast]
      rw [he]
      linarith [prime_reciprocal_squares_le N]

theorem heavy_omega_moment_bound : ∃ C : ℝ,0 < C ∧ ∀ N : ℕ,2 ≤ N →
    ∀ Q : Finset ℕ,(∀ n ∈ Q,0 < n ∧ n ≤ N) →
    (∑ n ∈ Q,heavyOmegaReciprocal n) ≤ C*(Real.log N)^(15/8:ℝ) := by
  classical
  obtain ⟨D,hD,herr⟩ := primeReciprocalLE_bounded_error
  refine ⟨Real.exp ((15/8:ℝ)*D+64),Real.exp_pos _,?_⟩
  intro N hN Q hQ
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (Nat.le_of_mem_primeFactorsList hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q,heavyOmegaReciprocal n) = ∑ n ∈ T,heavyOmegaReciprocal n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => heavyOmegaReciprocal n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=heavyOmegaReciprocal) (fun {_} hp => heavyOmegaReciprocal_norm hp) S
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have herror := (abs_le.mp (herr N (by exact_mod_cast hN))).2
  calc
    _ = ∑ n ∈ T,heavyOmegaReciprocal n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S,heavyOmegaReciprocal n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => heavyOmegaReciprocal_nonneg n)
    _ = ∏ p ∈ S with p.Prime,(1-heavyOmegaReciprocal p)⁻¹ := hs.2.tsum_eq
    _ ≤ Real.exp ((15/8:ℝ)*primeReciprocalLE N+64) := heavy_omega_euler_product N
    _ ≤ Real.exp (((15/8:ℝ)*D+64)+(15/8:ℝ)*B N) := by
      apply Real.exp_le_exp.mpr
      linarith
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeavyOmegaTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The excessive-prime-factor exception at the five-log-log threshold. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma log_fifteen_eighths_lower : (5/8:ℝ) ≤ Real.log (15/8:ℝ) := by
  have hh := Real.sum_range_le_log_div (x:=7/23) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hh
  linarith

lemma heavy_factor_tail_weight {b : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 5*b ≤ (n.primeFactorsList.length:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp (-5*b*Real.log (15/8:ℝ))*heavyOmegaReciprocal n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (15/8:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (-5*b*Real.log (15/8:ℝ))*(15/8:ℝ)^n.primeFactorsList.length := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 15/8),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_right hbad hlog.le]
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [heavyOmegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

/-- In particular, the excessive-Omega exception is smaller than
`N / log(N)^(1+1/6)`, the largest saving required for the nice-value count. -/
theorem heavy_factor_tail_count : ∃ C : ℝ,0 < C ∧ ∀ N : ℕ,4 ≤ N →
    ∀ Q : Finset ℕ,(∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 5*B N ≤ (n.primeFactorsList.length:ℝ)) →
    (Q.card:ℝ) ≤ C*N*(Real.log N)^(-5/4:ℝ) := by
  obtain ⟨C,hC,hmoment⟩ := heavy_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro N hN Q hQ
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hB : 0 ≤ B N := (doubleLog_nat_pos hN).le
  have hm := hmoment N (by omega) Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hrec : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (-5*B N*Real.log (15/8:ℝ))*(∑ n ∈ Q,heavyOmegaReciprocal n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => heavy_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
  have he : Real.exp (-5*B N*Real.log (15/8:ℝ))*(Real.log N)^(15/8:ℝ) ≤
      (Real.log N)^(-5/4:ℝ) := by
    rw [Real.rpow_def_of_pos hlog,Real.rpow_def_of_pos hlog,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -5*B N*Real.log (15/8:ℝ)+B N*(15/8:ℝ) ≤ B N*(-5/4:ℝ)
    nlinarith only [mul_le_mul_of_nonneg_right log_fifteen_eighths_lower hB]
  have hc := card_le_endpoint_reciprocal Q N (fun n hn =>
    ⟨(hQ n hn).1,by exact_mod_cast (hQ n hn).2.1⟩)
  calc
    _ ≤ N*(Real.exp (-5*B N*Real.log (15/8:ℝ))*(C*(Real.log N)^(15/8:ℝ))) :=
      hc.trans (mul_le_mul_of_nonneg_left (hrec.trans
        (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)) (Nat.cast_nonneg N))
    _ = C*N*(Real.exp (-5*B N*Real.log (15/8:ℝ))*(Real.log N)^(15/8:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientPreimageBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete preimage bounds for the finite totient counting reductions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_le_shift_square {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ≤ (p-1)^2 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have he : p-1+1=p := by omega
  nlinarith

lemma radical_le_twice_shift_product_square (n : ℕ) :
    (∏ p ∈ n.primeFactors,p) ≤ 2*(∏ p ∈ n.primeFactors,(p-1))^2 := by
  let E := n.primeFactors.erase 2
  have hprod : (∏ p ∈ E,p) ≤ (∏ p ∈ E,(p-1))^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro p hp
    exact prime_le_shift_square (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Finset.mem_erase.mp hp).1
  by_cases h2 : 2 ∈ n.primeFactors
  · have hrad := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p) h2
    have hshift := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p-1) h2
    norm_num only [Nat.reduceSub,one_mul] at hshift
    rw [← hrad,← hshift]
    exact Nat.mul_le_mul_left 2 hprod
  · have hE : E=n.primeFactors := Finset.erase_eq_of_notMem h2
    rw [hE] at hprod
    omega

lemma totient_preimage_quadratic {n : ℕ} (hn : 0 < n) : n ≤ 2*n.totient^2 := by
  let r := ∏ p ∈ n.primeFactors,p
  let s := ∏ p ∈ n.primeFactors,(p-1)
  have hr : 0 < r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hs : 0 < s := Finset.prod_pos (fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  obtain ⟨w,hw⟩ := n.prod_primeFactors_dvd
  change n=r*w at hw
  have hw0 : 0 < w := by nlinarith
  have he := Nat.totient_mul_prod_primeFactors n
  change n.totient*r=n*s at he
  have hφ : n.totient=w*s := by
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [Nat.mul_comm r n.totient,he,hw]
    ring
  have hrad : r ≤ 2*s^2 := radical_le_twice_shift_product_square n
  rw [hφ,hw]
  nlinarith [Nat.mul_le_mul_right w hrad,show w ≤ w^2 by nlinarith]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PreimageLoglogBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform range for every preimage of every totient up to x. -/
noncomputable section
namespace TotientAsymptotic

lemma doubleLog_twice_square {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    B (2*x^2) ≤ 3*B x := by
  have hexp : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx2 : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr hexp).trans hx
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx2
  have hl : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx2
  have hB : 1 ≤ B x := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ))
      ((Real.le_log_iff_exp_le hx0).mpr hx)
    simpa only [Real.log_exp,B] using hh
  have he : Real.log (2*x^2)=Real.log 2+2*Real.log x := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx0.ne'),Real.log_pow]
    norm_num
  have hh : Real.log (2*x^2) ≤ 3*Real.log x := by
    rw [he]
    linarith [Real.log_two_lt_d9]
  have hlpos : 0 < Real.log (2*x^2) := by rw [he]; positivity
  have hlog := Real.log_le_log hlpos hh
  rw [Real.log_mul (by norm_num) (by linarith : Real.log x ≠ 0)] at hlog
  have h3 : Real.log (3:ℝ) ≤ 2 := by simpa only [show (3:ℝ)-1=2 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  change B (2*x^2) ≤ Real.log 3+B x at hlog
  linarith

theorem preimage_loglog_bound : ∃ C : ℝ,0 < C ∧
    ∀ x : ℝ,Real.exp (Real.exp 1) ≤ x → ∀ n : ℕ,0 < n → (n.totient:ℝ) ≤ x →
      (n:ℝ) ≤ C*x*B x := by
  obtain ⟨C,hC,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨3*C,by positivity,?_⟩
  intro x hx n hn hφ
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hx
  have hφ0 : (0:ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnX : (n:ℝ) ≤ 2*x^2 := by
    have hh : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0.le hφ 2) (by norm_num))
  have hX : Real.exp 2 ≤ 2*x^2 := by
    have he : 2 ≤ Real.exp (1:ℝ) := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hy : Real.exp 2 ≤ x := (Real.exp_le_exp.mpr he).trans hx
    nlinarith
  have hh := (hratio (2*x^2) hX n hn hnX).trans
    (mul_le_mul_of_nonneg_left (doubleLog_twice_square hx) hC.le)
  have hnonneg : 0 ≤ C*(3*B x) := (div_pos (by exact_mod_cast hn) hφ0).le.trans hh
  calc
    (n:ℝ) = ((n:ℝ)/n.totient)*n.totient := (div_mul_cancel₀ _ hφ0.ne').symm
    _ ≤ (C*(3*B x))*n.totient := mul_le_mul_of_nonneg_right hh hφ0.le
    _ ≤ (C*(3*B x))*x := mul_le_mul_of_nonneg_left hφ hnonneg
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeSquareCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts for repeated large prime factors in values and their preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma large_square_count (N K : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ ∃ d : ℕ,K < d ∧ d^2 ∣ n) :
    (Q.card:ℝ) ≤ 2*N/(K+1:ℕ) := by
  classical
  let P := Finset.Ioo K (N+1)
  let M := fun d : ℕ => (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ d^2 ∣ n)
  have hsub : Q ⊆ P.biUnion M := by
    intro n hn
    obtain ⟨hn0,hnN,d,hKd,hd⟩ := hQ n hn
    have hd1 : 1 ≤ d := by omega
    have hdn : d ≤ n := (by nlinarith : d ≤ d^2).trans (Nat.le_of_dvd hn0 hd)
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_Ioo.mpr ⟨hKd,by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn0.ne',hd⟩⟩
  have hterm (d : ℕ) (hd : d ∈ P) : ((M d).card:ℝ) ≤ N/(d:ℝ)^2 := by
    have hd0 : 0 < d := by have := (Finset.mem_Ioo.mp hd).1; omega
    have hh : (M d).card=N/d^2 := Nat.card_multiples' N (d^2)
    rw [hh]
    have hle : (N/d^2)*d^2 ≤ N := Nat.div_mul_le_self N (d^2)
    apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℝ)<d by exact_mod_cast hd0))).mpr
    exact_mod_cast hle
  calc
    _ ≤ ((P.biUnion M).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ P,((M d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion M).card ≤ ∑ d ∈ P,(M d).card)
    _ ≤ ∑ d ∈ P,N/(d:ℝ)^2 := Finset.sum_le_sum hterm
    _ = N*(∑ d ∈ P,((d:ℝ)^2)⁻¹) := by rw [Finset.mul_sum]; simp only [div_eq_mul_inv]
    _ ≤ N*(2/(K+1:ℕ)) := mul_le_mul_of_nonneg_left
      (by simpa [P,Nat.cast_add,Nat.cast_one] using (sum_Ioo_inv_sq_le (α:=ℝ) K (N+1))) (Nat.cast_nonneg N)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquarePreimageCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large-square exceptions may occur in any preimage of a totient value. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma large_square_preimage_count (N K : ℕ) (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n ≤ N ∧ n.totient=v ∧
      ∃ d : ℕ,K < d ∧ d^2 ∣ n) :
    (Q.card:ℝ) ≤ 2*N/(K+1:ℕ) := by
  classical
  let A := (Finset.Icc 1 N).filter (fun n => ∃ d : ℕ,K < d ∧ d^2 ∣ n)
  have hsub : Q ⊆ A.image Nat.totient := by
    intro v hv
    obtain ⟨n,hn,hN,hφ,hd⟩ := hQ v hv
    exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn,hN⟩,hd⟩,hφ⟩
  have hc : (Q.card:ℝ) ≤ A.card :=
    Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
  exact hc.trans (large_square_count N K A (by
    intro n hn
    obtain ⟨hn,hd⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2,hd⟩))

/-- Uniformly counts values with a repeated large factor in some preimage.
The log-log preimage bound applies to every preimage, so no least-preimage
choice or fiber bound is involved. -/
theorem square_preimage_exception_count : ∃ C : ℝ,0 < C ∧
    ∀ x : ℝ,Real.exp (Real.exp 1) ≤ x → ∀ K : ℕ,∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
      ∃ d : ℕ,K < d ∧ d^2 ∣ n) →
    (Q.card:ℝ) ≤ C*x*B x/(K+1:ℕ) := by
  obtain ⟨C,hC,hbound⟩ := preimage_loglog_bound
  refine ⟨2*C,by positivity,?_⟩
  intro x hx K Q hQ
  have hpositive : 0 ≤ C*x*B x := by
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
    have hBx : 1 ≤ B x := by
      have hh := Real.log_le_log (Real.exp_pos (Real.exp 1)) hx
      rw [Real.log_exp] at hh
      have hlogx : 0 < Real.log x := (Real.exp_pos 1).trans_le hh
      have ht := Real.log_le_log (Real.exp_pos 1) hh
      simpa only [B,Real.log_exp] using ht
    positivity
  have hb := large_square_preimage_count ⌊C*x*B x⌋₊ K Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hd⟩ := hQ v hv
    refine ⟨n,hn,Nat.le_floor ?_,hφ,hd⟩
    exact hbound x hx n hn (by rwa [hφ]))
  calc
    _ ≤ 2*(⌊C*x*B x⌋₊:ℝ)/(K+1:ℕ) := hb
    _ ≤ 2*(C*x*B x)/(K+1:ℕ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hpositive) (by norm_num)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RegularValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete regular-value exception used in the Ford counting bootstrap. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem regular_value_exception_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X : ℕ),4 ≤ X → Real.exp (Real.exp 1) ≤ X → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬CountingRegular S X v) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+
      (2*X+D*X*B X)/(S+1:ℕ)+((nonNormalValues S X).card:ℝ) := by
  obtain ⟨C,hC,hheavy⟩ := heavy_factor_tail_count
  obtain ⟨D,hD,hsquare⟩ := square_preimage_exception_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X hX hx Q hQ
  let A := Q.filter (fun v => ¬(v.primeFactorsList.length:ℝ) ≤ 5*B X)
  let Vsq := Q.filter (fun v => ¬SquarefreeAbove v S)
  let Psq := Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧ ¬SquarefreeAbove n S)
  have hA : (A.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ) :=
    hheavy X hX A (by
      intro v hv
      obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
      exact ⟨isTotient_pos (hQ v hv).1,(hQ v hv).2.1,le_of_lt (lt_of_not_ge hbad)⟩)
  have hVsq : (Vsq.card:ℝ) ≤ 2*X/(S+1:ℕ) :=
    large_square_count X S Vsq (by
      intro v hv
      obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
      unfold SquarefreeAbove at hbad
      push Not at hbad
      obtain ⟨p,hp,hSp,hpv⟩ := hbad
      exact ⟨isTotient_pos (hQ v hv).1,(hQ v hv).2.1,p,by exact_mod_cast hSp,hpv⟩)
  have hPsq : (Psq.card:ℝ) ≤ D*X*B X/(S+1:ℕ) :=
    hsquare X hx S Psq (by
      intro v hv
      obtain ⟨hv,n,hn,hφ,hbad⟩ := Finset.mem_filter.mp hv
      unfold SquarefreeAbove at hbad
      push Not at hbad
      obtain ⟨p,hp,hSp,hpn⟩ := hbad
      exact ⟨n,hn,hφ,by exact_mod_cast (hQ v hv).2.1,p,by exact_mod_cast hSp,hpn⟩)
  have hcover : Q ⊆ A ∪ Vsq ∪ Psq ∪ nonNormalValues S X := by
    intro v hv
    by_cases hA' : (v.primeFactorsList.length:ℝ) ≤ 5*B X
    · by_cases hV : SquarefreeAbove v S
      · by_cases hP : ∀ n : ℕ,0 < n → n.totient=v → SquarefreeAbove n S
        · have hbad : ¬∀ n : ℕ,0 < n → n.totient=v → ∀ p ∈ n.primeFactors,IsNormalPrime S p := by
            intro hh
            exact (hQ v hv).2.2 ⟨hA',hV,fun n hn hφ => ⟨hP n hn hφ,hh n hn hφ⟩⟩
          push Not at hbad
          obtain ⟨n,hn,hφ,p,hp,hbad⟩ := hbad
          have hp' := Nat.mem_primeFactors.mp hp
          have hvX : v ∈ totientValues X := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨isTotient_pos (hQ v hv).1,by simpa using (hQ v hv).2.1⟩,(hQ v hv).1⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvX,n,p,hn,hφ,hp'.1,hp'.2.1,hbad⟩)
        · push Not at hP
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hP⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hv,hV⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hA'⟩)))
  have hcard : (Q.card:ℝ) ≤ A.card+Vsq.card+Psq.card+(nonNormalValues S X).card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  calc
    _ ≤ (A.card:ℝ)+Vsq.card+Psq.card+(nonNormalValues S X).card := hcard
    _ ≤ C*X*(Real.log X)^(-5/4:ℝ)+2*X/(S+1:ℕ)+D*X*B X/(S+1:ℕ)+
        (nonNormalValues S X).card := by linarith only [hA,hVsq,hPsq]
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LoglogGrid
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer cutoffs on the unit log-log grid used in Ford's counting argument. -/
noncomputable section
namespace TotientAsymptotic

lemma loglogCutoff_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ loglogCutoff b ∧ b-1 ≤ B (loglogCutoff b) ∧ B (loglogCutoff b) ≤ b ∧
      Real.log (loglogCutoff b) ≤ Real.exp b := by
  have he : 3 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have he4 : 4 ≤ Real.exp (Real.exp b) := by linarith [Real.add_one_le_exp (Real.exp b)]
  have hf := log_floor_lower he4
  change 2 ≤ loglogCutoff b ∧ _ at hf
  have hn1 : (1:ℝ) < loglogCutoff b := by exact_mod_cast (show 1 < loglogCutoff b by omega)
  have hl0 : 0 < Real.log (loglogCutoff b) := Real.log_pos hn1
  have hlu : Real.log (loglogCutoff b) ≤ Real.exp b := by
    have hh := Real.log_le_log (by linarith : (0:ℝ)<loglogCutoff b)
      (Nat.floor_le (Real.exp_pos (Real.exp b)).le)
    simpa only [Real.log_exp] using hh
  have hll : Real.exp b/2 ≤ Real.log (loglogCutoff b) := by
    simpa only [Real.log_exp,loglogCutoff] using hf.2
  have hBl : b-Real.log 2 ≤ B (loglogCutoff b) := by
    have hh := Real.log_le_log (by positivity : 0 < Real.exp b/2) hll
    simpa only [Real.log_div (Real.exp_ne_zero b) (by norm_num : (2:ℝ)≠0),Real.log_exp,B] using hh
  have hl2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hBu : B (loglogCutoff b) ≤ b := by
    have hh := Real.log_le_log hl0 hlu
    simpa only [B,Real.log_exp] using hh
  exact ⟨hf.1,by linarith,hBu,hlu⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoffs for the initial two-coordinate counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma eventually_bootstrap_log_budget (D : ℝ) : ∀ᶠ b : ℝ in atTop,
    10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b := by
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/40000 by norm_num)
  let E := Real.log 20+|D|+Real.log 2+10
  filter_upwards [hlog,eventually_ge_atTop (1:ℝ),eventually_ge_atTop (20000*E)] with b hb hb1 hbE
  have hb0 : 0 < b := by linarith
  have hl : Real.log b ≤ b/40000 := by
    have hh := (le_abs_self (Real.log b)).trans (by simpa only [Real.norm_eq_abs,abs_of_pos hb0,id_eq] using hb)
    linarith
  have hp : Real.log (b+1) ≤ Real.log 2+Real.log b := by
    have hh := Real.log_le_log (by linarith : 0 < b+1) (show b+1 ≤ 2*b by linarith)
    rwa [Real.log_mul (by norm_num : (2:ℝ)≠0) hb0.ne'] at hh
  rw [Real.log_mul (by norm_num : (20:ℝ)≠0) hb0.ne']
  dsimp [E] at hbE
  linarith

lemma bootstrap_cutoff_bounds {b : ℝ} (hb : 300000000 ≤ b)
    (hl : Real.log (20*b)+2 ≤ b/10000) :
    2 ≤ bootstrapBottom b ∧ bootstrapBottom b ≤ bootstrapTop b ∧
      (bootstrapBottom b:ℝ)+2 ≤ b/2 ∧ (bootstrapTop b:ℝ) ≤ b ∧
      b-Real.log (20*b)-2 ≤ bootstrapTop b ∧
      Real.exp (bootstrapTop b) ≤ Real.exp b/(20*b) := by
  have hb0 : 0 < b := by linarith
  have hlog0 : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have ht : 2 ≤ b-Real.log (20*b) := by linarith
  have hfloor2 : 2 ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.le_floor ht
  have hbot2 : 2 ≤ bootstrapBottom b := by
    apply Nat.le_floor
    linarith
  have hbotup : (bootstrapBottom b:ℝ) ≤ b/100000000 := Nat.floor_le (by positivity)
  have htopup : (bootstrapTop b:ℝ) ≤ b-Real.log (20*b) := by
    have hs : bootstrapTop b ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.sub_le _ _
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by linarith))
  have htoplow : b-Real.log (20*b)-2 ≤ bootstrapTop b := by
    dsimp [bootstrapTop]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊b-Real.log (20*b)⌋₊),Nat.cast_one]
    linarith [Nat.sub_one_lt_floor (b-Real.log (20*b))]
  refine ⟨hbot2,?_,by linarith,by linarith,htoplow,?_⟩
  · exact_mod_cast (show (bootstrapBottom b:ℝ) ≤ bootstrapTop b by linarith)
  · calc
      _ ≤ Real.exp (b-Real.log (20*b)) := Real.exp_le_exp.mpr htopup
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by positivity : 0 < 20*b)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SqrtCountingCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete cutoff between the fourth-root and square-root scales. -/
noncomputable section
namespace TotientAsymptotic

lemma sqrt_counting_cutoff {x : ℝ} (hx : 256 ≤ x) :
    4 ≤ ⌊Real.sqrt x⌋₊ ∧ ((⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x) ∧
      x^(1/4:ℝ) ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hy16 : 16 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith : (16:ℝ)^2 ≤ x)
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hn : 4 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (show (4:ℝ) ≤ Real.sqrt x by linarith)
  have hs : (⌊Real.sqrt x⌋₊:ℝ)^2 ≤ x := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊Real.sqrt x⌋₊) (Nat.floor_le hy0) 2
    rwa [Real.sq_sqrt hx0] at hh
  have hroot : x^(1/4:ℝ)=Real.sqrt (Real.sqrt x) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx0]
    norm_num
  have hhalf : Real.sqrt (Real.sqrt x) ≤ Real.sqrt x/2 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hy16]
  have hf : Real.sqrt x/2 ≤ (⌊Real.sqrt x⌋₊:ℝ) := by
    linarith [Nat.sub_one_lt_floor (Real.sqrt x)]
  exact ⟨hn,hs,hroot ▸ hhalf.trans hf⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformNonNormalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform form of the non-normal-prime value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem uniform_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (J : ℕ),2 < S → 0 ≤ B S → 256 ≤ x → 1 ≤ J →
    x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,D,hC,hD,hcount⟩ := non_normal_value_count_split
  refine ⟨C+5*D,by positivity,?_⟩
  intro S x J hS hBS hx hJ hxJ Q hQ
  let N := ⌊Real.sqrt x⌋₊
  let L := Nat.clog 2 N
  have hcut := sqrt_counting_cutoff hx
  have hN : 4 ≤ N := hcut.1
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNx : (N:ℝ) ≤ x := by nlinarith only [hcut.2.1,hNR]
  have hNJ : N ≤ 2^J := by exact_mod_cast hNx.trans hxJ
  have hLJ : L ≤ J := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hNJ
  have hb := dyadic_nat_bounds (show 1 < N by omega)
  have hL1 : 1 ≤ L := hb.1
  have hLlog : 1+Real.log L ≤ 1+Real.log J := by
    exact add_le_add le_rfl (Real.log_le_log (by exact_mod_cast (show 0 < L by omega))
      (by exact_mod_cast hLJ))
  have hLlog0 : 0 ≤ 1+Real.log L := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ L by exact_mod_cast hL1)
    linarith
  have hJlog1 : 1 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
    linarith
  have hpow2x : (2:ℝ)^L ≤ 2*x := by nlinarith only [hb.2.1,hNx]
  have hBsmall0 : 0 ≤ B ((2:ℝ)^L) := by
    have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
    have hh := (doubleLog_nat_pos h4).le
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hB : B ((2:ℝ)^L) ≤ B (2*x) := by
    have hp : (1:ℝ) < 2^L := by
      have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
      exact_mod_cast (show 1 < (2:ℕ)^L by omega)
    exact Real.log_le_log (Real.log_pos hp) (Real.log_le_log (by positivity) hpow2x)
  have hB0 : 0 ≤ B (2*x) := hBsmall0.trans hB
  have hmass : (B ((2:ℝ)^L))^5*(1+Real.log L) ≤ (B (2*x))^5*(1+Real.log J) :=
    mul_le_mul (pow_le_pow_left₀ hBsmall0 hB 5) hLlog hLlog0 (pow_nonneg hB0 _)
  have hE1 : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hE0 : 0 ≤ dyadicTotientEnvelope J := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hsn : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlogS.le _
  have hlarge : 1+4*dyadicTotientEnvelope J*(1+Real.log J) ≤
      5*dyadicTotientEnvelope J*(1+Real.log J) := by
    have hh := mul_le_mul hE1 hJlog1 (by norm_num) hE0
    nlinarith only [hh]
  have hs : C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (show 0 ≤ C*dyadicTotientEnvelope J*x/Real.log x by positivity)) hsn
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hl : (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      (1+4*dyadicTotientEnvelope J*(1+Real.log J)) ≤
      (5*D)*dyadicTotientEnvelope J*x/Real.log x*(B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlarge
      (show 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc := hcount S x N J hS hBS hN (by linarith) hcut.2.1 hcut.2.2 hJ hxJ Q hQ
  exact hc.trans ((add_le_add hs hl).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapNormalityDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normality parameter chosen for the bootstrap gives exponential decay
in the log-log scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma loglogCutoff_ge_four {b : ℝ} (hb : 2 ≤ b) : 4 ≤ loglogCutoff b := by
  have he : 3 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  apply Nat.le_floor
  have hh := Real.add_one_le_exp (Real.exp b)
  norm_num
  linarith

lemma bootstrap_normality_factor {b : ℝ} (hb : 300000000 ≤ b) :
    let S := loglogCutoff (bootstrapBottom b)
    2 < (S:ℝ) ∧ 0 ≤ B S ∧
      (Real.log S)^(-1/6:ℝ) ≤ Real.exp (1/3:ℝ)*Real.exp (-b/600000000) := by
  let L := bootstrapBottom b
  have hL : 2 ≤ L := Nat.le_floor (show (2:ℝ) ≤ b/100000000 by linarith)
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hB := loglogCutoff_bounds hLR
  have h4 := loglogCutoff_ge_four hLR
  have hS : (2:ℝ) < loglogCutoff L := by exact_mod_cast (show 2 < loglogCutoff L by omega)
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by linarith)
  have hBlower : b/100000000-2 ≤ B (loglogCutoff L) := by
    have hh : b/100000000-1 < (L:ℝ) := Nat.sub_one_lt_floor (b/100000000)
    linarith only [hh,hB.2.1]
  refine ⟨hS,by linarith only [hB.2.1,hLR],?_⟩
  rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change B (loglogCutoff L)*(-1/6:ℝ) ≤ (1/3:ℝ)+ -b/600000000
  linarith

lemma shifted_sixth_exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun b : ℝ => (b+2)^6*Real.exp (-c*b)) atTop (nhds 0) := by
  have ht : Tendsto (fun b : ℝ => b+2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro t
    filter_upwards [eventually_ge_atTop (t-2)] with b hb
    linarith
  have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6:ℝ) c hc).comp ht).const_mul
    (Real.exp (2*c))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [] with b
  have he : Real.exp (-c*b)=Real.exp (2*c)*Real.exp (-c*(b+2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [Function.comp_apply]
  have hpow : (b+2)^(6:ℝ)=(b+2)^(6:ℕ) := Real.rpow_natCast (b+2) 6
  rw [hpow,he]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicLogGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary log-log comparisons at dyadic endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma dyadic_B_tendsto : Tendsto (fun J : ℕ => B ((2:ℝ)^J)) atTop atTop :=
  B_tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))

lemma double_log_double_le {x : ℝ} (hx : 2 ≤ x) : B (2*x) ≤ B x+1 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : Real.log (2:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog : Real.log (2*x) ≤ 2*Real.log x := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne']
    linarith
  have hp : 0 < Real.log (2*x) := Real.log_pos (by linarith)
  have hh := Real.log_le_log hp hlog
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hl.ne'] at hh
  have htwo : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  change Real.log (Real.log (2*x)) ≤ Real.log (Real.log x)+1
  linarith

lemma dyadic_log_index_le {J : ℕ} (hJ : 1 ≤ J) :
    1+Real.log J ≤ B ((2:ℝ)^J)+2 := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  rw [dyadic_endpoint_B,Real.log_mul hJ0.ne' hlog2.ne']
  have hh : Real.log (1/2:ℝ) ≤ Real.log (Real.log (2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith [Real.log_two_gt_d9])
  norm_num only [Real.log_div,Real.log_one] at hh
  linarith [Real.log_two_lt_d9]

lemma dyadic_normality_polynomial {J : ℕ} (hJ : 1 ≤ J)
    (hb : 0 ≤ B ((2:ℝ)^J)) :
    (B (2*(2:ℝ)^J))^5*(1+Real.log J) ≤ (B ((2:ℝ)^J)+2)^6 := by
  have hx : (2:ℝ) ≤ 2^J := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ
    simpa using hh
  have hB := double_log_double_le hx
  have hB0 : 0 ≤ B (2*(2:ℝ)^J) := by
    have hmono : B ((2:ℝ)^J) ≤ B (2*(2:ℝ)^J) :=
      Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by positivity) (by nlinarith only [hx]))
    exact hb.trans hmono
  have hlog := dyadic_log_index_le hJ
  have hlog0 : 0 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
    linarith
  calc
    _ ≤ (B ((2:ℝ)^J)+2)^5*(B ((2:ℝ)^J)+2) :=
      mul_le_mul (pow_le_pow_left₀ hB0 (hB.trans (by linarith)) 5) hlog hlog0 (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapNonNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normality exception is small relative to the finite counting envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_non_normal_exception : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ (2:ℝ)^J ∧ ¬IsNormalPrime (loglogCutoff (bootstrapBottom (B ((2:ℝ)^J)))) p) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  obtain ⟨C,hC,hcount⟩ := uniform_non_normal_value_count
  let ε := fun J : ℕ => (C*Real.exp (1/3:ℝ))*
    ((B ((2:ℝ)^J)+2)^6*Real.exp (-B ((2:ℝ)^J)/600000000))
  have hlim : Tendsto ε atTop (nhds 0) := by
    have hh := ((shifted_sixth_exp_decay (by norm_num : (0:ℝ)<1/600000000)).comp dyadic_B_tendsto).const_mul
      (C*Real.exp (1/3:ℝ))
    convert hh using 1
    · funext J
      dsimp only [ε,Function.comp_apply]
      rw [show -(1/600000000:ℝ)*B ((2:ℝ)^J) = -B ((2:ℝ)^J)/600000000 by ring]
    · simp
  refine ⟨ε,hlim,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [dyadic_B_tendsto.eventually (eventually_ge_atTop 300000000),
    hxlim.eventually (eventually_ge_atTop 256),eventually_ge_atTop (1:ℕ)] with J hb hx hJ
  let b := B ((2:ℝ)^J)
  let S := loglogCutoff (bootstrapBottom b)
  have hs := bootstrap_normality_factor hb
  change 2 < (S:ℝ) ∧ 0 ≤ B S ∧ (Real.log S)^(-1/6:ℝ) ≤
    Real.exp (1/3:ℝ)*Real.exp (-b/600000000) at hs
  have hb0 : 0 ≤ b := by dsimp [b] <;> linarith
  have hpoly := dyadic_normality_polynomial hJ hb0
  have hlog : 0 < Real.log ((2:ℝ)^J) := Real.log_pos (by linarith)
  have hE0 : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  have hcoef : 0 ≤ C*dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J) := by positivity
  have hnorm0 : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg
    (Real.log_pos (by linarith : (1:ℝ)<S)).le _
  have hm := mul_le_mul hpoly hs.2.2 hnorm0 (pow_nonneg (by linarith : 0 ≤ b+2) 6)
  intro Q hQ
  have hh := hcount S ((2:ℝ)^J) J hs.1 hs.2.1 hx hJ le_rfl Q hQ
  have hu := mul_le_mul_of_nonneg_left hm hcoef
  apply hh.trans
  calc
    _ = (C*dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J))*
        ((B (2*(2:ℝ)^J))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ)) := by ring
    _ ≤ _ := hu
    _ = _ := by dsimp [ε,b] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapSquareDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor cutoff is much larger than every fixed logarithmic power. -/
noncomputable section
namespace TotientAsymptotic

lemma exp_quadratic_lower {u : ℝ} (hu : 0 ≤ u) : u^2/4 ≤ Real.exp u := by
  have he := Real.add_one_le_exp (u/2)
  have hhalf : 0 ≤ u/2 := by linarith
  have hs : (u/2)^2 ≤ (Real.exp (u/2))^2 :=
    pow_le_pow_left₀ hhalf (by linarith) 2
  have hid : (Real.exp (u/2))^2=Real.exp u := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hid] at hs
  nlinarith only [hs]

lemma bootstrap_square_cutoff {b : ℝ} (hb : 1000000000000000000 ≤ b) :
    Real.exp (3*b) ≤ (loglogCutoff (bootstrapBottom b):ℝ) := by
  let L := bootstrapBottom b
  let S := loglogCutoff L
  have hL : 2 ≤ L := Nat.le_floor (show (2:ℝ) ≤ b/100000000 by linarith)
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hs := loglogCutoff_bounds hLR
  have hS4 := loglogCutoff_ge_four hLR
  have hS0 : (0:ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hBl : b/200000000 ≤ B S := by
    have hh : b/100000000-1 < (L:ℝ) := Nat.sub_one_lt_floor (b/100000000)
    linarith only [hh,hs.2.1,hb]
  have hB0 : 0 ≤ B S := by linarith
  have hsquare : 3*b ≤ (B S)^2/4 := by
    have hh := pow_le_pow_left₀ (show (0:ℝ) ≤ b/200000000 by linarith) hBl 2
    have hb2 : 1000000000000000000*b ≤ b^2 := by nlinarith only [hb]
    nlinarith only [hh,hb2]
  have hlog : 3*b ≤ Real.log S := by
    have hh := hsquare.trans (exp_quadratic_lower hB0)
    rwa [B,Real.exp_log hlogS] at hh
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hS0)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All failures of regularity are negligible relative to the finite envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_regularity_exception : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ 2^J ∧
      ¬CountingRegular (loglogCutoff (bootstrapBottom (B ((2:ℝ)^J)))) ((2:ℝ)^J) v) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  classical
  obtain ⟨C,D,hC,hD,hreg⟩ := regular_value_exception_count
  obtain ⟨η,hη,hnormal⟩ := bootstrap_non_normal_exception
  have he0 : Tendsto (fun b : ℝ => Real.exp (-b/4)) atTop (nhds 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/4) (by norm_num)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext b
    simp only [Real.rpow_zero,one_mul]
    congr 1
    ring
  have he2 : Tendsto (fun b : ℝ => Real.exp (-2*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) 2 (by norm_num))
  have hb2 : Tendsto (fun b : ℝ => b*Real.exp (-2*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) 2 (by norm_num))
  let ε := fun J : ℕ => C*Real.exp (-B ((2:ℝ)^J)/4)+2*Real.exp (-2*B ((2:ℝ)^J))+
    D*(B ((2:ℝ)^J)*Real.exp (-2*B ((2:ℝ)^J)))+η J
  have hlim : Tendsto ε atTop (nhds 0) := by
    have hh := ((((he0.comp dyadic_B_tendsto).const_mul C).add
      ((he2.comp dyadic_B_tendsto).const_mul 2)).add
      ((hb2.comp dyadic_B_tendsto).const_mul D)).add hη
    simpa only [Function.comp_apply,mul_zero,add_zero] using hh
  refine ⟨ε,hlim,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hnormal,dyadic_B_tendsto.eventually (eventually_ge_atTop 1000000000000000000),
    hxlim.eventually (eventually_ge_atTop (Real.exp (Real.exp 1))),eventually_ge_atTop (2:ℕ)]
    with J hnormal hb hx hJ
  let x := (2:ℝ)^J
  let b := B x
  let S := loglogCutoff (bootstrapBottom b)
  have hb0 : 0 ≤ b := by dsimp [b,x] <;> linarith
  have hx0 : 0 < x := by dsimp [x] <;> positivity
  have hX4 : 4 ≤ (2:ℕ)^J := by
    have hh : (2:ℕ)^2 ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hJ
    simpa using hh
  have hx4 : (4:ℝ) ≤ x := by
    change (4:ℝ) ≤ (2:ℝ)^J
    exact_mod_cast hX4
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hE1 : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hbase : 0 ≤ x/Real.log x := by positivity
  have hbaseE : x/Real.log x ≤ dyadicTotientEnvelope J*x/Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hE1 hbase
    simpa only [one_mul,mul_div_assoc] using hh
  have hinv : (Real.log x)⁻¹=Real.exp (-b) := by
    rw [Real.exp_neg,show Real.exp b=Real.log x from Real.exp_log hlog]
  have hS : Real.exp (3*b) ≤ (S:ℝ) := bootstrap_square_cutoff hb
  have hSplus : Real.exp (3*b) ≤ (S+1:ℕ) := by push_cast <;> linarith
  have hrec : ((S+1:ℕ):ℝ)⁻¹ ≤ Real.exp (-3*b) := by
    have hh := inv_anti₀ (Real.exp_pos (3*b)) hSplus
    simpa only [← Real.exp_neg,neg_mul] using hh
  intro Q hQ
  have hmain := hreg S (2^J) hX4 (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hx) Q (by
    intro v hv
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQ v hv)
  have hN := hnormal (nonNormalValues S x) (by
    intro v hv
    obtain ⟨hv,n,p,hn,hφ,hp,hpn,hbad⟩ := Finset.mem_filter.mp hv
    have hval := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    exact ⟨n,p,hn,hφ,hp,hpn,(Nat.cast_le.mpr hval).trans (Nat.floor_le hx0.le),hbad⟩)
  have hheavy : C*x*(Real.log x)^(-5/4:ℝ) ≤
      C*Real.exp (-b/4)*(dyadicTotientEnvelope J*x/Real.log x) := by
    have hid : C*x*(Real.log x)^(-5/4:ℝ)=C*Real.exp (-b/4)*(x/Real.log x) := by
      have hpow : (Real.log x)^(-5/4:ℝ)=Real.exp (-b/4)*Real.exp (-b) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        dsimp [b,B]
        ring
      rw [hpow]
      simp only [div_eq_mul_inv,hinv]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hbaseE (by positivity)
  have hsquare : (2*x+D*x*b)/(S+1:ℕ) ≤
      (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(dyadicTotientEnvelope J*x/Real.log x) := by
    have hpos : 0 ≤ 2*x+D*x*b := by positivity
    have hh := mul_le_mul_of_nonneg_left hrec hpos
    have hid : (2*x+D*x*b)*Real.exp (-3*b)=
        (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(x/Real.log x) := by
      rw [div_eq_mul_inv,hinv]
      have he : Real.exp (-3*b)=Real.exp (-2*b)*Real.exp (-b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    calc
      _ ≤ (2*x+D*x*b)*Real.exp (-3*b) := by simpa only [div_eq_mul_inv] using hh
      _ = _ := hid
      _ ≤ _ := mul_le_mul_of_nonneg_left hbaseE (by positivity)
  have hmain' : (Q.card:ℝ) ≤ C*x*(Real.log x)^(-5/4:ℝ)+
      (2*x+D*x*b)/(S+1:ℕ)+(nonNormalValues S x).card := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hmain
  calc
    _ ≤ C*x*(Real.log x)^(-5/4:ℝ)+(2*x+D*x*b)/(S+1:ℕ)+(nonNormalValues S x).card := hmain'
    _ ≤ C*Real.exp (-b/4)*(dyadicTotientEnvelope J*x/Real.log x)+
        (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(dyadicTotientEnvelope J*x/Real.log x)+
        η J*(dyadicTotientEnvelope J*x/Real.log x) := by linarith only [hheavy,hsquare,hN]
    _ = _ := by dsimp [ε,b,x] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapGridError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the explicit two-coordinate grid and normality errors. -/
noncomputable section
namespace TotientAsymptotic

lemma bootstrap_grid_error {b D u : ℝ} {K : ℕ} (hb : 1 ≤ b)
    (_hu0 : 0 ≤ u) (hu : u ≤ b/100000000) (hK : (K:ℝ) ≤ b)
    (hKlow : b-Real.log (20*b)-2 ≤ K)
    (hbudget : 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b) :
    (3/2:ℝ)*(b+5-K)+4*u+5*D+8*Real.sqrt (u*K)+2*Real.log (K+1:ℕ) ≤ b/200 := by
  have hb0 : 0 ≤ b := by linarith
  have hlog0 : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hlogK : Real.log (K+1:ℕ) ≤ Real.log (b+1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hmul : u*(K:ℝ) ≤ (b/100000000)*b :=
    mul_le_mul hu hK (Nat.cast_nonneg K) (by positivity)
  have hsqrt : Real.sqrt (u*K) ≤ b/10000 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hmul]
  have hD : D ≤ |D| := le_abs_self D
  nlinarith only [hKlow,hu,hsqrt,hlogK,hbudget,hD,hlog0,hlogb,hb]

lemma bootstrap_grid_exponential {b D u : ℝ} {K : ℕ} (hb : 1 ≤ b)
    (hu0 : 0 ≤ u) (hu : u ≤ b/100000000) (hK : (K:ℝ) ≤ b)
    (hKlow : b-Real.log (20*b)-2 ≤ K)
    (hbudget : 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b) :
    ((K+1:ℕ):ℝ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+4*u+5*D+
      8*Real.sqrt (u*K)) ≤ Real.exp (-(201/200:ℝ)*b) := by
  have he := bootstrap_grid_error hb hu0 hu hK hKlow hbudget
  have hpos : (0:ℝ) < (K+1:ℕ) := by positivity
  have hpow : ((K+1:ℕ):ℝ)^2 = Real.exp (Real.log (K+1:ℕ)+Real.log (K+1:ℕ)) := by
    rw [Real.exp_add,Real.exp_log hpos]
    ring
  rw [hpow,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapViolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A power-saving two-coordinate exception, with fixed explicit cutoffs. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- The regular part of Ford Lemma 4.2 at the single parameter needed to
start the global counting bootstrap. -/
theorem bootstrap_regular_violation : ∃ C : ℝ,0 < C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,v ≤ X ∧ CountingRegular (loglogCutoff (bootstrapBottom (B X))) X v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (101/100:ℝ)*B X < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-201/200:ℝ) := by
  obtain ⟨C,D,hC,hD,hcount⟩ := two_coordinate_violation_count
  refine ⟨C,hC,?_⟩
  have ht : Tendsto (fun X : ℕ => B X) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_bootstrap_log_budget D),
    ht.eventually (eventually_ge_atTop 300000000),eventually_ge_atTop (4:ℕ)] with X hbudget hb hX
  let b := B X
  let K := bootstrapTop b
  let L := bootstrapBottom b
  change 300000000 ≤ b at hb
  have hb0 : 0 ≤ b := by linarith
  have hlb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hl : Real.log (20*b)+2 ≤ b/10000 := by
    change 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b at hbudget
    nlinarith only [hbudget,abs_nonneg D,hlb]
  have hc := bootstrap_cutoff_bounds hb hl
  change 2 ≤ L ∧ L ≤ K ∧ (L:ℝ)+2 ≤ b/2 ∧ (K:ℝ) ≤ b ∧
    b-Real.log (20*b)-2 ≤ K ∧ Real.exp K ≤ Real.exp b/(20*b) at hc
  obtain ⟨hL,hLK,hLB,hKB,hKlow,hcut⟩ := hc
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have he : Real.exp b=Real.log X := Real.exp_log hlogX
  rw [he] at hcut
  have hS := loglogCutoff_bounds (by exact_mod_cast hL : (2:ℝ) ≤ L)
  have hS0 : 0 ≤ B (loglogCutoff L) := by
    have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
    linarith only [hS.2.1,hLR]
  have hSu : B (loglogCutoff L) ≤ b/100000000 :=
    hS.2.2.1.trans (Nat.floor_le (by positivity : 0 ≤ b/100000000))
  have herr := bootstrap_grid_exponential (by linarith : 1 ≤ b) hS0 hSu hKB hKlow hbudget
  intro Q hQ
  have hh := hcount X K L (1/100) hX (by change 12 ≤ b; linarith) (by norm_num)
    hL hLK hLB (by linarith) hcut Q (by
      intro v hv
      obtain ⟨hvX,hreg,n,hn,hφ,hbad⟩ := hQ v hv
      refine ⟨hvX,hreg,n,hn,hφ,?_⟩
      convert hbad using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  have hconst : (1:ℝ)+1/100=101/100 := by norm_num
  rw [hconst] at hh
  calc
    _ ≤ C*X*(K+1:ℕ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+
        4*B (loglogCutoff L)+5*D+8*Real.sqrt (B (loglogCutoff L)*K)) := hh
    _ = C*X*(((K+1:ℕ):ℝ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+
        4*B (loglogCutoff L)+5*D+8*Real.sqrt (B (loglogCutoff L)*K))) := by ring
    _ ≤ C*X*Real.exp (-(201/200:ℝ)*b) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos hlogX]; dsimp [b,B]; congr 2; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapGoodValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The surviving values satisfy the bootstrap inequality for every preimage. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_good_value_discard_oai : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ 2^J ∧ ¬BootstrapGood ((2:ℝ)^J) v) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  classical
  obtain ⟨δ,hδ,hreg⟩ := bootstrap_regularity_exception
  obtain ⟨C,hC,hviol⟩ := bootstrap_regular_violation
  let ε := fun J : ℕ => δ J+C*Real.exp (-B ((2:ℝ)^J)/200)
  have he : Tendsto (fun b : ℝ => Real.exp (-b/200)) atTop (nhds 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/200) (by norm_num)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext b
    simp only [Real.rpow_zero,one_mul]
    congr 1
    ring
  have hε : Tendsto ε atTop (nhds 0) := by
    have hh := hδ.add ((he.comp dyadic_B_tendsto).const_mul C)
    simpa only [Function.comp_apply,mul_zero,add_zero] using hh
  refine ⟨ε,hε,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℕ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hreg,hxlim.eventually hviol,eventually_ge_atTop (1:ℕ)] with J hreg hviol hJ
  let x := (2:ℝ)^J
  let S := loglogCutoff (bootstrapBottom (B x))
  have hx1 : 1 < x := by
    have hh : (2:ℕ) ≤ 2^J := by
      have ht : (2:ℕ)^1 ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hJ
      simpa using ht
    change (1:ℝ) < (2:ℝ)^J
    exact_mod_cast (show 1 < (2:ℕ)^J by omega)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hE : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hscale : 0 ≤ x/Real.log x := by positivity
  have hscaleE : x/Real.log x ≤ dyadicTotientEnvelope J*x/Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hE hscale
    simpa only [one_mul,mul_div_assoc] using hh
  intro Q hQ
  let A := Q.filter (fun v => ¬CountingRegular S x v)
  let T := Q\A
  have hA := hreg A (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hbad⟩)
  have hT := hviol T (by
    intro v hv
    obtain ⟨hv,hvA⟩ := Finset.mem_sdiff.mp hv
    have hr : CountingRegular S x v := by
      by_contra hh
      exact hvA (Finset.mem_filter.mpr ⟨hv,hh⟩)
    have hf : ¬∀ n : ℕ,0 < n → n.totient=v →
        a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x := by
      intro hh
      exact (hQ v hv).2.2 ⟨hr,hh⟩
    push Not at hf
    obtain ⟨n,hn,hφ,hbad⟩ := hf
    refine ⟨(hQ v hv).2.1,?_,n,hn,hφ,?_⟩
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hr
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbad)
  have hT' : (T.card:ℝ) ≤ C*Real.exp (-B x/200)*(dyadicTotientEnvelope J*x/Real.log x) := by
    have ht : (T.card:ℝ) ≤ C*x*(Real.log x)^(-201/200:ℝ) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hT
    have hid : C*x*(Real.log x)^(-201/200:ℝ)=C*Real.exp (-B x/200)*(x/Real.log x) := by
      have hinv : (Real.log x)⁻¹=Real.exp (-B x) := by rw [Real.exp_neg,B,Real.exp_log hlog]
      have hp : (Real.log x)^(-201/200:ℝ)=Real.exp (-B x/200)*Real.exp (-B x) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        unfold B
        ring
      rw [hp]
      simp only [div_eq_mul_inv,hinv]
      ring
    exact ht.trans (hid ▸ mul_le_mul_of_nonneg_left hscaleE (by positivity))
  have hcard : (Q.card:ℝ)=(A.card:ℝ)+(T.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show A ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=A.card+T.card by dsimp [T]; omega)
  rw [hcard]
  calc
    _ ≤ δ J*(dyadicTotientEnvelope J*x/Real.log x)+
        C*Real.exp (-B x/200)*(dyadicTotientEnvelope J*x/Real.log x) := add_le_add hA hT'
    _ = _ := by dsimp [ε,x] <;> ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.bootstrap_good_value_discard_oai := @OAI.TotientAsymptotic.bootstrap_good_value_discard_oai
