-- Prove2me | solution 1 for OAI.TotientAsymptotic.full_coordinate_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:35:18.135928+00:00
-- url     : https://prove2.me/submissions/5b061ff2-a11a-4dde-9b9d-66a872ffaaae

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

section
-- module Solutions.OAIQ233_TA.Compat
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuralInput
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal structural inputs from Ford, *The distribution of totients*,
arXiv:1104.3264v2 (14 July 2013), Theorems 10 and 16.

The exceptional sets count values with **some** failing preimage, as in the
convention preceding Theorem 10, p. 5.  Consequently every preimage of a value
outside the exceptional set satisfies the property.  Ford's coordinates in
(4.2), p. 17, are clamped double logarithms.  Theorem 16, (6.1)--(6.2), p. 29,
also supplies the terminal lower bound that allows removing this clamp.

The band center below is Ford's B*rho^i*(1-i/m), not the phase-dependent
`bandScale` in Basic.lean.  Passing between these two centers is an additional
analytic step, governed by the manuscript's equation alpha-comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fordPrimeCoordinate_eq_raw_of_pos {n i : ℕ}
    (h : 0 < fordPrimeCoordinate n i) :
    fordPrimeCoordinate n i = primeDoubleLog n i := by
  have hraw : 0 < primeDoubleLog n i :=
    (lt_max_iff.mp h).resolve_left (lt_irrefl 0)
  exact max_eq_right hraw.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma omegaIn_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (U T : ℝ) :
    omegaIn (∏ i ∈ s, f i) U T = ∑ i ∈ s, omegaIn (f i) U T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omegaIn]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      omegaIn_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma normality_interval_bounds {S U T ε : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hSU : S ≤ U) (hUT : U < T)
    (hTp : T ≤ (p-1 : ℕ)) (hε : Real.sqrt (B S * B T) ≤ ε) :
    B T-B U-ε ≤ (omegaIn (p-1) U T : ℝ) ∧
      (omegaIn (p-1) U T : ℝ) ≤ B T-B U+ε := by
  have h := abs_lt.mp (hp.2.2 U T hSU hUT hTp)
  constructor <;> linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordFactorization
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordPrime_eq_get {n i : ℕ} (hi : i < n.primeFactorsList.length) :
    fordPrime n i = n.primeFactorsList.reverse[i]'(by simpa using hi) := by
  unfold fordPrime
  rw [show n.primeFactorsList.reverse[i]? = some (n.primeFactorsList.reverse[i]'(by simpa using hi)) from
    List.getElem?_eq_getElem _]
  rfl

lemma fordPrime_prime {n i : ℕ} (hi : i < n.primeFactorsList.length) : (fordPrime n i).Prime := by
  rw [fordPrime_eq_get hi]
  exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.getElem_mem _))

lemma fordPrime_antitone {n i j : ℕ} (hi : i < n.primeFactorsList.length)
    (hj : j < n.primeFactorsList.length) (hij : i ≤ j) : fordPrime n j ≤ fordPrime n i := by
  rw [fordPrime_eq_get hi,fordPrime_eq_get hj]
  exact (Nat.primeFactorsList_sorted n).reverse.getElem_ge_getElem_of_le hij

lemma fordPrime_index_of_doubleLog_pos {n i : ℕ} (h : 0 < primeDoubleLog n i) :
    i < n.primeFactorsList.length := by
  by_contra! hi
  have he : fordPrime n i=1 := by
    unfold fordPrime
    rw [show n.primeFactorsList.reverse[i]? = none from List.getElem?_eq_none (by simpa using hi)]
    rfl
  simp [primeDoubleLog,he] at h

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveError
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

lemma odd_sieve_divisor_weight {z d : ℕ} (hd : d ∣ ∏ p ∈ oddSievePrimes z,p) :
    (3:ℕ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
  have hsq := (oddSievePrimes_prod_squarefree z).squarefree_of_dvd hd
  have hlen : ArithmeticFunction.cardDistinctFactors d ≤ d.primeFactorsList.length :=
    d.primeFactorsList.dedup_sublist.length_le
  calc
    _ ≤ 3^d.primeFactorsList.length := Nat.pow_le_pow_right (by norm_num) hlen
    _ ≤ d.primeFactorsList.prod := List.pow_card_le_prod _ 3 (by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactorsList hp
      have hmem := mem_oddSievePrimes_of_dvd hprime ((Nat.dvd_of_mem_primeFactorsList hp).trans hd)
      have hh := mem_oddSievePrimes.mp hmem
      have := hprime.two_le
      omega)
    _ = d := Nat.prod_primeFactorsList hsq.ne_zero

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

lemma shiftedPrimeCutoff_scale {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    8*Real.log 4*(2+Real.log (shiftedPrimeCutoff L)) ≤
      Real.log (Real.exp (L/4)) := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hh := (shiftedPrimeCutoff_bounds hL).2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0≤8*Real.log 4 by positivity)
  have he : 8*Real.log 4*(L/(128*Real.log 4))=L/16 := by field_simp <;> ring
  rw [he] at hm
  rw [Real.log_exp]
  nlinarith

lemma shiftedPrimeCutoff_error {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    (shiftedPrimeCutoff L:ℝ)+2*(Real.exp (L/4))^3 ≤
      96*Real.exp L/L^2 := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0<L := by nlinarith
  have he : (Real.exp (L/4))^3 = Real.exp (3*L/4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hquad := Real.quadratic_le_exp_of_nonneg (by positivity : 0≤L/4)
  have hsmall : L^2 ≤ 32*Real.exp (L/4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3*L/4)).le
  have hsum : Real.exp (L/4)*Real.exp (3*L/4)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : 3*Real.exp (3*L/4) ≤ 96*Real.exp L/L^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonSizes
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer size and large-prime-part bounds for Ford's comparison hypotheses. -/

noncomputable section

namespace TotientAsymptotic

lemma partBelow_bound (n : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (partBelow n Z : ℝ) ≤ Z^n.primeFactorsList.length := by
  let l := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)
  have hb (l : List ℕ) (hl : ∀ p ∈ l, (p : ℝ) ≤ Z) :
      (l.map (fun p : ℕ => (p : ℝ))).prod ≤ Z^l.length := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hp := hl p (by simp)
      have ht := ih (fun q hq => hl q (by simp [hq]))
      have hn : 0 ≤ (l.map (fun p : ℕ => (p : ℝ))).prod :=
        List.prod_nonneg (by simp)
      simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using
        mul_le_mul hp ht hn (zero_le_one.trans hZ)
  have hp : ((l.map (fun p : ℕ => (p : ℝ))).prod) ≤ Z^l.length := by
    apply hb
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  have hc : (partBelow n Z : ℝ)=(l.map (fun p : ℕ => (p : ℝ))).prod := by
    exact Nat.cast_list_prod l
  rw [hc]
  exact hp.trans (pow_le_pow_right₀ hZ (List.length_filter_le _ _))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeFactorBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic of the prime-factor bands in Ford's collision argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_pos (n : ℕ) (V : ℝ) : 0 < partBelow n V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBetween_pos (n : ℕ) (U V : ℝ) : 0 < partBetween n U V := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

lemma partBetween_factors (n : ℕ) (U V : ℝ) :
    (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)).Perm
      (partBetween n U V).primeFactorsList := by
  apply Nat.primeFactorsList_unique rfl
  intro p hp
  exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1

lemma partBetween_omega (n : ℕ) (U V : ℝ) :
    (partBetween n U V).primeFactorsList.length=omegaIn n U V :=
  (partBetween_factors n U V).length_eq.symm

lemma partBetween_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (U V : ℝ) :
    partBetween (n*m) U V=partBetween n U V*partBetween m U V := by
  have hh := (Nat.perm_primeFactorsList_mul hn hm).filter
    (fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))
  simpa [partBetween,List.filter_append,List.prod_append] using hh.prod_eq

lemma partBelow_band_split (n : ℕ) {U V : ℝ} (hUV : U ≤ V) :
    partBelow n U*partBetween n U V=partBelow n V := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p:ℝ) ≤ U) id
    (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V))
  have hleft : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => (p:ℝ) ≤ U)=n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ U) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    by_cases h : (p:ℝ) ≤ U
    · simp [h,h.trans hUV]
    · simp [h]
  have hright : (n.primeFactorsList.filter (fun p : ℕ => (p:ℝ) ≤ V)).filter
      (fun p : ℕ => ¬(p:ℝ) ≤ U)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    congr 1
    funext p
    simp [not_le]
  simpa only [List.map_id,hleft,hright,partBelow,partBetween] using hh

lemma partBetween_dvd {n : ℕ} (hn : n ≠ 0) (U V : ℝ) : partBetween n U V ∣ n := by
  have hh := (List.filter_sublist (p:=fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))
    (l:=n.primeFactorsList)).prod_dvd_prod
  obtain ⟨c,hc⟩ := hh
  exact ⟨c,by simpa only [partBetween,Nat.prod_primeFactorsList hn] using hc⟩

lemma partBetween_squarefree {n : ℕ} (hn : n ≠ 0) {U V : ℝ}
    (hsq : SquarefreeAbove n U) : Squarefree (partBetween n U V) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hpband : p ∈ (partBetween n U V).primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd (partBetween_pos n U V).ne' hp).mpr
      ((dvd_mul_right p p).trans hd)
  have hpf := (partBetween_factors n U V).mem_iff.mpr hpband
  have hbound : U < (p:ℝ) ∧ (p:ℝ) ≤ V := of_decide_eq_true (List.mem_filter.mp hpf).2
  have hpU := hbound.1
  apply hsq p hp hpU
  simpa only [pow_two] using hd.trans (partBetween_dvd hn U V)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBandProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicative and nested-truncation identities for actual collision bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_support (n : ℕ) (U V : ℝ) {p : ℕ}
    (hp : p ∈ (partBetween n U V).primeFactorsList) : U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
  have hm := (partBetween_factors n U V).mem_iff.mpr hp
  exact of_decide_eq_true (List.mem_filter.mp hm).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientFibers_FiniteFiber
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace TotientFibers

theorem totient_prime_prod {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    Nat.totient (∏ p ∈ Q, p) = ∏ p ∈ Q, (p - 1) := by
  have hpos : 0 < ∏ p ∈ Q, p := Finset.prod_pos fun p hp => (hQ p hp).pos
  apply Nat.mul_right_cancel hpos
  simpa only [Nat.primeFactors_prod hQ, mul_comm] using
    Nat.totient_mul_prod_primeFactors (∏ p ∈ Q, p)

end TotientFibers

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalTotientBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal prime divisors of a preimage force many factors in its totient bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma omegaIn_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) (U V : ℝ) :
    omegaIn a U V ≤ omegaIn b U V := by
  obtain ⟨c,rfl⟩ := hab
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [omegaIn_mul ha.ne' hc]
  omega

lemma shifted_prime_product_dvd_totient {n : ℕ} (P : Finset ℕ)
    (hP : P ⊆ n.primeFactors) : (∏ p ∈ P,(p-1)) ∣ n.totient := by
  have hp : ∀ p ∈ P,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
  have hd : (∏ p ∈ P,p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset P n.primeFactors id hP).trans n.prod_primeFactors_dvd
  have hφ := Nat.totient_dvd_of_dvd hd
  rwa [TotientFibers.totient_prime_prod hp] at hφ

lemma normal_prime_totient_band_lower {n : ℕ} (hn : 0 < n) (P : Finset ℕ)
    (hP : P ⊆ n.primeFactors) {S U V : ℝ}
    (hSU : S ≤ U) (hUV : U < V)
    (hnormal : ∀ p ∈ P,IsNormalPrime S p)
    (hlarge : ∀ p ∈ P,V ≤ (p-1:ℕ)) :
    (P.card:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  have hp : ∀ p ∈ P,p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
  have hpos : 0 < ∏ p ∈ P,(p-1) := Finset.prod_pos (fun p hmem => by have := (hp p hmem).two_le; omega)
  have hlower (p : ℕ) (hmem : p ∈ P) :
      B V-B U-Real.sqrt (B S*B V) ≤ (omegaIn (p-1) U V:ℝ) :=
    (normality_interval_bounds (hnormal p hmem) hSU hUV (hlarge p hmem) le_rfl).1
  have hs := Finset.sum_le_sum hlower
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hω := omegaIn_dvd hpos (Nat.totient_pos.mpr hn) (shifted_prime_product_dvd_totient P hP) U V
  have hωR : (omegaIn (∏ p ∈ P,(p-1)) U V:ℝ) ≤ (omegaIn n.totient U V:ℝ) := by exact_mod_cast hω
  rw [omegaIn_prod _ _ (fun p hmem => by have := (hp p hmem).two_le; omega),Nat.cast_sum] at hωR
  exact hs.trans hωR

lemma omegaIn_partBetween (n : ℕ) {S F U V : ℝ} (hSU : S ≤ U) (hVF : V ≤ F) :
    omegaIn (partBetween n S F) U V=omegaIn n U V := by
  have he := ((partBetween_factors n S F).filter
    (fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ V))).length_eq
  have hf : (n.primeFactorsList.filter (fun p : ℕ => S < (p:ℝ) ∧ (p:ℝ) ≤ F)).filter
      (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)=
      n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) := by
    simp only [List.filter_filter]
    apply List.filter_congr
    intro p _
    by_cases h : U < (p:ℝ) ∧ (p:ℝ) ≤ V
    · simp [h,hSU.trans_lt h.1,h.2.trans hVF]
    · simp [h]
  simpa only [hf,omegaIn] using he.symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordLargePrimeCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's ordered prime coordinates give the required number of distinct large primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_prefix_omega_lower {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n.primeFactorsList.length)
    {U : ℝ} (hU : U < (fordPrime n (k-1):ℝ)) :
    k ≤ omegaIn n U n := by
  let l := n.primeFactorsList.reverse
  let P := fun p : ℕ => decide (U < (p:ℝ) ∧ (p:ℝ) ≤ n)
  have htake : (l.take k).filter P=l.take k := by
    apply List.filter_eq_self.mpr
    intro p hp
    have hpfull : p ∈ n.primeFactorsList :=
      List.mem_reverse.mp (List.mem_of_mem_take hp)
    have hpn : (p:ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primeFactorsList hpfull
    apply decide_eq_true
    refine ⟨?_,hpn⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    have hik : i < k := by
      have hh : (l.take k).length=min k l.length := List.length_take
      omega
    have hin : i < n.primeFactorsList.length := by omega
    have he' : fordPrime n i=p := by
      rw [fordPrime_eq_get hin]
      simpa only [l,List.getElem_take] using he
    rw [← he']
    have hord : fordPrime n (k-1) ≤ fordPrime n i :=
      fordPrime_antitone hin (by omega) (by omega)
    exact hU.trans_le (by exact_mod_cast hord)
  have hsub := (List.take_sublist k l).filter P
  rw [htake] at hsub
  have hh := hsub.length_le
  have hkl : k ≤ l.length := by simpa [l] using hkn
  rw [List.length_take,min_eq_left hkl] at hh
  simpa only [l,P,List.filter_reverse,List.length_reverse,omegaIn] using hh

lemma distinctPrimesAbove_subset {n : ℕ} (hn : 0 < n) (U : ℝ) :
    distinctPrimesAbove n U ⊆ n.primeFactors := by
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (Nat.dvd_of_mem_primeFactors hp).trans (partBetween_dvd hn.ne' U n),hn.ne'⟩

lemma distinctPrimesAbove_large (n : ℕ) (U : ℝ) {p : ℕ}
    (hp : p ∈ distinctPrimesAbove n U) : U < (p:ℝ) := by
  have hp' : p ∈ (partBetween n U n).primeFactorsList := List.mem_toFinset.mp hp
  exact (partBetween_support n U n hp').1

lemma distinctPrimesAbove_card {n : ℕ} (hn : 0 < n) {U : ℝ} (hsq : SquarefreeAbove n U) :
    (distinctPrimesAbove n U).card=omegaIn n U n := by
  rw [distinctPrimesAbove,squarefree_primeFactors_card (partBetween_squarefree hn.ne' hsq),
    partBetween_omega]

lemma ford_prefix_distinct_primes {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {U : ℝ}
    (hU : U < (fordPrime n (k-1):ℝ)) (hsq : SquarefreeAbove n U) :
    k ≤ (distinctPrimesAbove n U).card := by
  rw [distinctPrimesAbove_card hn hsq]
  exact ford_prefix_omega_lower hk hkn hU

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordNormalBandLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower interval-factor counts forced by Ford's actual ordered preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normal_large_prime_band_lower {n k U V : ℕ} (hn : 0 < n)
    {S : ℝ} (hSU : S ≤ U) (hUV : U ≤ V)
    (hcard : k ≤ (distinctPrimesAbove n V).card)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  let A := B V-B U-Real.sqrt (B S*B V)
  by_cases hA : 0 ≤ A
  · by_cases he : U=V
    · subst V
      dsimp [A] at hA ⊢
      have hs := Real.sqrt_nonneg (B S*B U)
      have ho : (0:ℝ) ≤ omegaIn n.totient U U := Nat.cast_nonneg _
      nlinarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
    have hlarge (p : ℕ) (hp : p ∈ distinctPrimesAbove n V) : (V:ℝ) ≤ (p-1:ℕ) := by
      have hVp : V < p := by exact_mod_cast distinctPrimesAbove_large n V hp
      exact_mod_cast (show V ≤ p-1 by omega)
    have hb := normal_prime_totient_band_lower hn (distinctPrimesAbove n V)
      (distinctPrimesAbove_subset hn V) hSU (by exact_mod_cast (lt_of_le_of_ne hUV he))
      (fun p hp => hnormal p (distinctPrimesAbove_subset hn V hp)) hlarge
    have hc : (k:ℝ) ≤ (distinctPrimesAbove n V).card := Nat.cast_le.mpr hcard
    exact (mul_le_mul_of_nonneg_right hc hA).trans hb
  · have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hω : (0:ℝ) ≤ omegaIn n.totient U V := Nat.cast_nonneg _
    exact (mul_nonpos_of_nonneg_of_nonpos hk (le_of_lt (lt_of_not_ge hA))).trans hω

lemma ford_normal_band_lower {n k U V : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {S : ℝ}
    (hSU : S ≤ U) (hUV : U ≤ V) (hVp : V < fordPrime n (k-1))
    (hsq : SquarefreeAbove n V)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤ (omegaIn n.totient U V:ℝ) := by
  apply normal_large_prime_band_lower hn hSU hUV _ hnormal
  exact ford_prefix_distinct_primes hn hk hkn (by exact_mod_cast hVp) hsq

lemma ford_normal_part_band_lower {n k U V : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ≤ n.primeFactorsList.length) {S F : ℝ}
    (hSU : S ≤ U) (hUV : U ≤ V) (hVF : (V:ℝ) ≤ F) (hVp : V < fordPrime n (k-1))
    (hsq : SquarefreeAbove n V)
    (hnormal : ∀ p ∈ n.primeFactors,IsNormalPrime S p) :
    (k:ℝ)*(B V-B U-Real.sqrt (B S*B V)) ≤
      (omegaIn (partBetween n.totient S F) U V:ℝ) := by
  rw [omegaIn_partBetween n.totient hSU hVF]
  exact ford_normal_band_lower hn hk hkn hSU hUV hVp hsq hnormal

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquarefreeBandTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-factor-count tail used in Ford's upper count of totient values. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma squarefree_lower_factor_mass (S Q : Finset ℕ) {c R H : ℝ} (hc : 1 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S ∧ R ≤ (n.primeFactors.card:ℝ))
    (hH : (∑ p ∈ S,(p:ℝ)⁻¹) ≤ H) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp (c*H-R*Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm := squarefree_reciprocal_moment S Q hc0.le
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have ht : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ c^(-R)*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hpow := Real.rpow_le_rpow_of_exponent_le hc (hQ n hn).2.2
    rw [Real.rpow_natCast] at hpow
    have he : c^(-R)*c^R=1 := by
      rw [← Real.rpow_add hc0]
      simp
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hc0.le (-R))
    rw [he] at hh
    have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ (n:ℝ)⁻¹ by positivity)
    simpa only [div_eq_mul_inv,mul_assoc,one_mul] using hmul
  calc
    _ ≤ c^(-R)*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := ht
    _ ≤ c^(-R)*Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hc0.le (-R))
    _ ≤ c^(-R)*Real.exp (c*H) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc0.le (-R))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hH hc0.le)
    _ = _ := by
      rw [Real.rpow_def_of_pos hc0,← Real.exp_add]
      congr 1
      ring

theorem squarefree_band_lower_mass : ∃ D : ℝ,0 < D ∧
    ∀ U V c R : ℝ,2 ≤ U → U ≤ V → 1 ≤ c → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,Squarefree n ∧
      (∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) ∧
      R ≤ (n.primeFactorsList.length:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp (c*(B V-B U+D)-R*Real.log c) := by
  obtain ⟨D,hD,hprime⟩ := prime_interval_upper_bounded_error
  refine ⟨D,hD,?_⟩
  intro U V c R hU hUV hc Q hQ
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  apply squarefree_lower_factor_mass S Q hc _ (hprime U V hU hUV)
  intro n hn
  refine ⟨(hQ n hn).1,?_,?_⟩
  · intro p hp
    have hp' : p ∈ n.primeFactorsList := List.mem_toFinset.mp hp
    have hb := (hQ n hn).2.1 p hp'
    exact Finset.mem_filter.mpr ⟨(primesUpTo_mem (by linarith : 0 ≤ V)).mpr
      ⟨Nat.prime_of_mem_primeFactorsList hp',hb.2⟩,hb.1⟩
  · rw [squarefree_primeFactors_card (hQ n hn).1]
    exact (hQ n hn).2.2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteFactorMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite factorization turns independent interval masses into a product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_factor_reciprocal_mass {k : ℕ} (Q : Finset ℕ) (f : ℕ → Fin k → ℕ)
    (hf : ∀ n ∈ Q,∏ j,f n j=n) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ ∏ j,∑ d ∈ Q.image (fun n => f n j),(d:ℝ)⁻¹ := by
  classical
  let T : Fin k → Finset ℕ := fun j => Q.image (fun n => f n j)
  have hi : Set.InjOn f (↑Q : Set ℕ) := by
    intro n hn m hm he
    rw [← hf n hn,← hf m hm,he]
  have hs : Q.image f ⊆ Fintype.piFinset T := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_image.mpr ⟨n,hn,rfl⟩)
  calc
    _ = ∑ n ∈ Q,∏ j,(f n j:ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      conv_lhs => rw [← hf n hn]
      rw [Nat.cast_prod,Finset.prod_inv_distrib]
    _ = ∑ t ∈ Q.image f,∏ j,(t j:ℝ)⁻¹ := by
      symm
      rw [Finset.sum_image hi]
    _ ≤ ∑ t ∈ Fintype.piFinset T,∏ j,(t j:ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun t _ _ =>
        Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    _ = _ := (Finset.prod_univ_sum T (fun (_ : Fin k) (d : ℕ) => (d:ℝ)⁻¹)).symm

theorem finite_squarefree_band_mass : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (U V c R : Fin k → ℝ),
    (∀ j,2 ≤ U j) → (∀ j,U j ≤ V j) → (∀ j,1 ≤ c j) →
    ∀ (Q : Finset ℕ) (f : ℕ → Fin k → ℕ),
    (∀ n ∈ Q,∏ j,f n j=n) →
    (∀ n ∈ Q,∀ j,Squarefree (f n j) ∧
      (∀ p ∈ (f n j).primeFactorsList,U j < (p:ℝ) ∧ (p:ℝ) ≤ V j) ∧
      R j ≤ ((f n j).primeFactorsList.length:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (∑ j : Fin k,(c j*(B (V j)-B (U j)+D)-R j*Real.log (c j))) := by
  obtain ⟨D,hD,hbound⟩ := squarefree_band_lower_mass
  refine ⟨D,hD,?_⟩
  intro k U V c R hU hUV hc Q f hf hQ
  apply (finite_factor_reciprocal_mass Q f hf).trans
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro j _
    exact Finset.sum_nonneg (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  · intro j _
    apply hbound (U j) (V j) (c j) (R j) (hU j) (hUV j) (hc j)
    intro d hd
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
    exact hQ n hn j

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete one-dimensional sieve for integers avoiding a prime interval. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma mem_intervalSievePrimes {S z p : ℕ} :
    p ∈ intervalSievePrimes S z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 ∧ S < p := by
  simp only [intervalSievePrimes,Finset.mem_filter,mem_oddSievePrimes,and_assoc]

lemma intervalSieveDensity_squarefree {d : ℕ} (hd : Squarefree d) :
    intervalSieveDensity d = (d:ℝ)⁻¹ := by
  rw [intervalSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hd]

lemma count_divisible_modulus {d : ℕ} (hd : 0 < d) :
    Nat.count (fun n => d ∣ n) d = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have he : (Finset.range d).filter (fun n => d ∣ n) = {0} := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
    constructor
    · rintro ⟨hn,hdn⟩
      by_contra hne
      exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdn)
    · rintro rfl
      exact ⟨hd,dvd_zero d⟩
  rw [he,Finset.card_singleton]

lemma intervalPrimeSieve_rem_le (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    {d : ℕ} (hd : Squarefree d) :
    |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d| ≤ d+1 := by
  have hd0 := Nat.pos_of_ne_zero hd.ne_zero
  have hc := count_periodic_error d hd0 (fun n => d ∣ n)
    (fun n => by simp only [Nat.dvd_iff_mod_eq_zero,Nat.mod_mod]) X
  rw [count_divisible_modulus hd0] at hc
  norm_num only [Nat.cast_one,mul_one] at hc
  have hi := interval_count_discrepancy (fun n => d ∣ n) X
  have he : rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun n => d ∣ n)).card:ℝ)-(X:ℝ)/d := by
    simp only [rem,multSum,intervalPrimeSieve,Finset.sum_boole]
    rw [intervalSieveDensity_squarefree hd]
    ring
  rw [he]
  exact (abs_sub_le _ (Nat.count (fun n => d ∣ n) X:ℝ) _).trans
    ((add_le_add hi hc).trans_eq (by ring))

lemma intervalPrimeSieve_error_sum (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ (∏ p ∈ intervalSievePrimes S z,p).divisors,
      if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
        |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d| else 0) ≤ 2*y^3 := by
  classical
  let P : ℕ := ∏ p ∈ intervalSievePrimes S z,p
  let T : Finset ℕ := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ y)
  have hP := intervalSieve_squarefree S z
  have hT (d : ℕ) (hd : d ∈ T) : d ∣ P ∧ 1 ≤ d ∧ (d:ℝ) ≤ y := by
    obtain ⟨hd,hy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd,hP0⟩ := Nat.mem_divisors.mp hd
    have h0 : d ≠ 0 := by
      intro h
      subst d
      exact hP0 (zero_dvd_iff.mp hd)
    exact ⟨hd,Nat.one_le_iff_ne_zero.mpr h0,hy⟩
  have hcard : (T.card:ℝ) ≤ y := by
    have hsub : T ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro d hd
      exact Finset.mem_Icc.mpr ⟨(hT d hd).2.1,Nat.le_floor (hT d hd).2.2⟩
    have hc : (T.card:ℝ) ≤ ⌊y⌋₊ := by
      exact_mod_cast (by simpa using Finset.card_le_card hsub : T.card ≤ ⌊y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter]
  change (∑ d ∈ T,(3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
    |rem (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) d|) ≤ _
  calc
    _ ≤ ∑ _d ∈ T,2*y^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd,h1,hdy⟩ := hT d hd
      have hweight : (3:ℝ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
        exact_mod_cast odd_sieve_divisor_weight (hd.trans (intervalSieve_prod_dvd S z))
      have hr := intervalPrimeSieve_rem_le S X z y hy (hP.squarefree_of_dvd hd)
      have hdR : (1:ℝ) ≤ d := by exact_mod_cast h1
      have hh := mul_le_mul hweight hr (abs_nonneg _) (by positivity : (0:ℝ) ≤ d)
      nlinarith
    _ = (T.card:ℝ)*(2*y^2) := by simp
    _ ≤ y*(2*y^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma intervalSifted_selberg (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((intervalSifted S X z).card:ℝ) ≤
      X/selbergBoundingSum (intervalPrimeSieve S X z y hy)+2*y^3 := by
  have he : siftedSum (s := (intervalPrimeSieve S X z y hy).toBoundingSieve) =
      ((intervalSifted S X z).card:ℝ) := by
    change (∑ n ∈ Finset.Icc 1 X,
      if (∏ p ∈ intervalSievePrimes S z,p).Coprime n then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp [intervalSifted]
  rw [← he]
  exact (selberg_bound_simple _).trans
    (add_le_add le_rfl (intervalPrimeSieve_error_sum S X z y hy))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalSieveDenominator
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval sieve has the reciprocal Euler-product denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma intervalSieveWeight_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ intervalSieveWeight p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg zero_le_one (by linarith)

lemma intervalSieveWeight_density {p : ℕ} (hp : p.Prime) :
    intervalSieveWeight p = intervalSieveDensity p/(1-intervalSieveDensity p) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  rw [intervalSieveDensity_prime hp]
  dsimp [intervalSieveWeight]
  field_simp

lemma intervalSieveWeight_moment {p : ℕ} (hp : p.Prime) :
    intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p) = Real.log p/p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p:ℝ)-1 ≠ 0 := by linarith
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have he : 1+intervalSieveWeight p = (p:ℝ)/(p-1) := by
    unfold intervalSieveWeight
    field_simp
    ring
  rw [he]
  dsimp [intervalSieveWeight]
  field_simp

lemma intervalSieve_moment_le (S z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ intervalSievePrimes S z,
      intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p)) ≤
        Real.log 4*(2+Real.log z) := by
  calc
    _ = ∑ p ∈ intervalSievePrimes S z,Real.log p/p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact intervalSieveWeight_moment (mem_intervalSievePrimes.mp hp).2.1
    _ ≤ ∑ p ∈ (Finset.Icc 2 z).filter Nat.Prime,Real.log p/p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hh := mem_intervalSievePrimes.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hh.2.1.two_le,hh.1⟩,hh.2.1⟩
      · intro p hp _
        have hpp := (Finset.mem_filter.mp hp).2
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) (Nat.cast_nonneg _)
    _ ≤ _ := prime_log_mass_le z hz

lemma intervalSieveTerms_prod (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (T : Finset ℕ) (hT : T ⊆ intervalSievePrimes S z) :
    selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve (∏ p ∈ T,p) =
      ∏ p ∈ T,intervalSieveWeight p := by
  rw [(selbergTerms_mult _).map_prod_of_prime T
    (fun p hp => (mem_intervalSievePrimes.mp (hT hp)).2.1)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (mem_intervalSievePrimes.mp (hT hp)).2.1
  rw [SelbergSieve.selbergTerms_apply]
  simp only [hpp.primeFactors,Finset.prod_singleton]
  change intervalSieveDensity p*(1/(1-intervalSieveDensity p)) = _
  rw [intervalSieveWeight_density hpp]
  ring

lemma intervalSieveBoundingSum_powerset (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (intervalPrimeSieve S X z y hy) =
      ∑ T ∈ (intervalSievePrimes S z).powerset,
        if ((∏ p ∈ T,p:ℕ):ℝ)^2 ≤ y then ∏ p ∈ T,intervalSieveWeight p else 0 := by
  classical
  have hsq := intervalSieve_squarefree S z
  unfold selbergBoundingSum
  change (∑ d ∈ (∏ p ∈ intervalSievePrimes S z,p).divisors,
    if (d:ℝ)^2 ≤ y then selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve d else 0) = _
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero,Nat.factors_eq]
  simp only [List.toFinset_coe,Finset.prod_val]
  change (∑ T ∈ (∏ p ∈ intervalSievePrimes S z,p).primeFactors.powerset,
    if ((∏ p ∈ T,p:ℕ):ℝ)^2 ≤ y then
      selbergTerms (intervalPrimeSieve S X z y hy).toBoundingSieve (∏ p ∈ T,p) else 0) = _
  rw [Nat.primeFactors_prod (fun p hp => (mem_intervalSievePrimes.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [intervalSieveTerms_prod S X z y hy T (Finset.mem_powerset.mp hT)]

theorem intervalSieveBoundingSum_lower (S X z : ℕ) (y : ℝ) (hy : 1 < y)
    (hz : 2 ≤ z) (hscale : 4*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    (∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p))/2 ≤
      selbergBoundingSum (intervalPrimeSieve S X z y hy.le) := by
  classical
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hl : 0 < Real.log y/2 := by positivity
  have hm : (∑ p ∈ intervalSievePrimes S z,
      intervalSieveWeight p*Real.log p/(1+intervalSieveWeight p)) ≤ (Real.log y/2)/2 := by
    nlinarith [intervalSieve_moment_le S z hz]
  have hh := subset_weight_below_half (intervalSievePrimes S z) intervalSieveWeight
    (fun p => Real.log p)
    (fun p hp => intervalSieveWeight_nonneg (mem_intervalSievePrimes.mp hp).2.1)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (mem_intervalSievePrimes.mp hp).2.1.one_lt.le))
    hl hm
  apply hh.trans
  rw [intervalSieveBoundingSum_powerset]
  apply Finset.sum_le_sum
  intro T hT
  have hTp := Finset.mem_powerset.mp hT
  have hprimes : ∀ p ∈ T,p.Prime := fun p hp => (mem_intervalSievePrimes.mp (hTp hp)).2.1
  have hpos : (0:ℝ) < (∏ p ∈ T,p:ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (hprimes p hp).pos)
  have hlog : Real.log ((∏ p ∈ T,p:ℕ):ℝ) = ∑ p ∈ T,Real.log p := by
    rw [Nat.cast_prod,Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero)]
  split_ifs with hsmall hcut hcut
  · exact le_rfl
  · exfalso
    apply hcut
    apply (Real.log_le_log_iff (sq_pos_of_pos hpos) (by linarith : 0<y)).mp
    rw [Real.log_pow,hlog]
    norm_num
    linarith
  · exact Finset.prod_nonneg (fun p hp => intervalSieveWeight_nonneg (hprimes p hp))
  · exact le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalSieveEuler
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interval Euler-product lower bound from the already proved Mertens bound. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma intervalSieveWeight_euler {p : ℕ} (hp : p.Prime) :
    1+intervalSieveWeight p = (p:ℝ)/(p-1) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p:ℝ)-1 ≠ 0 := by linarith
  unfold intervalSieveWeight
  field_simp
  ring

lemma primeEulerProduct_interval {S z : ℕ} (hS : 2 ≤ S) (hSz : S ≤ z) :
    primeEulerProduct z = primeEulerProduct S*
      ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
  classical
  have he : (Finset.Icc 2 z).filter Nat.Prime =
      ((Finset.Icc 2 S).filter Nat.Prime) ∪ intervalSievePrimes S z := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_union,mem_intervalSievePrimes]
    constructor
    · rintro ⟨⟨hp2,hpz⟩,hpp⟩
      by_cases hpS : p ≤ S
      · exact Or.inl ⟨⟨hp2,hpS⟩,hpp⟩
      · exact Or.inr ⟨hpz,hpp,by omega,by omega⟩
    · rintro (⟨⟨hp2,hpS⟩,hpp⟩ | ⟨hpz,hpp,_,_⟩)
      · exact ⟨⟨hp2,hpS.trans hSz⟩,hpp⟩
      · exact ⟨⟨hpp.two_le,hpz⟩,hpp⟩
  have hd : Disjoint ((Finset.Icc 2 S).filter Nat.Prime) (intervalSievePrimes S z) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hj := (mem_intervalSievePrimes.mp hq).2.2.2
    omega
  unfold primeEulerProduct
  rw [he,Finset.prod_union hd]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (intervalSieveWeight_euler (mem_intervalSievePrimes.mp hp).2.1).symm

theorem intervalSieveEuler_lower : ∃ C : ℝ,0 < C ∧
    ∀ S z : ℕ,2 ≤ S → S ≤ z →
      Real.log z/(C*Real.log S) ≤ ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
  obtain ⟨C,hC,hbound⟩ := mertensProductInput
  refine ⟨C,hC,?_⟩
  intro S z hS hSz
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hprod : 0 ≤ ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hh := intervalSieveWeight_nonneg (mem_intervalSievePrimes.mp hp).2.1
    linarith
  apply (div_le_iff₀ (mul_pos hC hlogS)).mpr
  have he := primeEulerProduct_log_lower z
  rw [primeEulerProduct_interval hS hSz] at he
  have hb := mul_le_mul_of_nonneg_right (hbound S hS) hprod
  nlinarith

theorem intervalSifted_bound : ∃ C : ℝ,0 < C ∧
    ∀ S X z : ℕ,2 ≤ S → S ≤ z → ∀ y : ℝ,1 < y →
      4*Real.log 4*(2+Real.log z) ≤ Real.log y →
      ((intervalSifted S X z).card:ℝ) ≤ C*X*Real.log S/Real.log z+2*y^3 := by
  obtain ⟨C,hC,hCbound⟩ := intervalSieveEuler_lower
  refine ⟨2*C,by positivity,?_⟩
  intro S X z hS hSz y hy hscale
  have hz : 2 ≤ z := hS.trans hSz
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  let E := ∏ p ∈ intervalSievePrimes S z,(1+intervalSieveWeight p)
  have hE : Real.log z/(C*Real.log S) ≤ E := hCbound S z hS hSz
  have hB : E/2 ≤ selbergBoundingSum (intervalPrimeSieve S X z y hy.le) :=
    intervalSieveBoundingSum_lower S X z y hy hz hscale
  have hEl : 0 < E := lt_of_lt_of_le (div_pos hlogz (mul_pos hC hlogS)) hE
  have hd : (X:ℝ)/selbergBoundingSum (intervalPrimeSieve S X z y hy.le) ≤
      2*C*X*Real.log S/Real.log z := by
    calc
      _ ≤ (X:ℝ)/(E/2) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hB
      _ ≤ (X:ℝ)/((Real.log z/(C*Real.log S))/2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
      _ = _ := by field_simp
  exact (intervalSifted_selberg S X z y hy.le).trans (add_le_add hd le_rfl)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalAvoidance
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's interval-avoidance sieve, with natural-number endpoints. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma intervalSifted_card_le (S X z : ℕ) : (intervalSifted S X z).card ≤ X := by
  simpa [intervalSifted] using Finset.card_le_card
    (Finset.filter_subset (fun n => (∏ p ∈ intervalSievePrimes S z,p).Coprime n) (Finset.Icc 1 X))

lemma intervalSifted_antitone {S X z w : ℕ} (hwz : w ≤ z) :
    intervalSifted S X z ⊆ intervalSifted S X w := by
  intro n hn
  obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,?_⟩
  apply hcop.of_dvd_left
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  obtain ⟨hpw,hpp,hp2,hSp⟩ := mem_intervalSievePrimes.mp hp
  exact mem_intervalSievePrimes.mpr ⟨hpw.trans hwz,hpp,hp2,hSp⟩

lemma mem_intervalSifted {S X z n : ℕ} (hS : 2 ≤ S) :
    n ∈ intervalSifted S X z ↔ n ∈ Finset.Icc 1 X ∧
      ∀ p : ℕ,p.Prime → S < p → p ≤ z → ¬ p ∣ n := by
  constructor
  · intro hn
    obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
    refine ⟨hn,?_⟩
    intro p hp hSp hpz hpn
    have hmem := mem_intervalSievePrimes.mpr ⟨hpz,hp,by omega,hSp⟩
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem) hpn) hcop
  · rintro ⟨hn,havoid⟩
    refine Finset.mem_filter.mpr ⟨hn,?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpd hpn
    obtain ⟨q,hq,hpq⟩ := hp.prime.exists_mem_finset_dvd hpd
    have hqq := (mem_intervalSievePrimes.mp hq).2.1
    have he := (Nat.prime_dvd_prime_iff_eq hp hqq).mp hpq
    subst q
    have hmem := mem_intervalSievePrimes.mp hq
    exact havoid p hp hmem.2.2.2 hmem.1 hpn

/-- All cutoffs are uniform. The proof only uses the already proved concrete
Selberg error, finite Euler product, and explicit small-power cutoff. -/
theorem interval_avoidance_count : ∃ C : ℝ,0 < C ∧ ∀ S X z : ℕ,
    2 ≤ S → S ≤ z → z ≤ X →
      ((intervalSifted S X z).card:ℝ) ≤ C*X*Real.log S/Real.log z := by
  obtain ⟨C,hC,hbound⟩ := intervalSifted_bound
  let K : ℝ := 256*Real.log 4
  let D : ℝ := 4*K+C*K+192
  have hc : 1 ≤ Real.log (4:ℝ) := by
    have hh := Real.log_two_gt_d9
    have he : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  have hK : 1 ≤ K := by dsimp [K] <;> nlinarith
  refine ⟨D,by dsimp [D] <;> positivity,?_⟩
  intro S X z hS hSz hzX
  have hS1 : (1:ℝ) < S := by exact_mod_cast (show 1 < S by omega)
  have hz1 : (1:ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hX1 : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlS : 0 < Real.log S := Real.log_pos hS1
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have hLX : 0 < Real.log X := Real.log_pos hX1
  have hSl : (1/2:ℝ) ≤ Real.log S := by
    have hh : Real.log (2:ℝ) ≤ Real.log S :=
      Real.log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast hS)
    linarith [Real.log_two_gt_d9]
  have hlzX : Real.log z ≤ Real.log X := Real.log_le_log (by linarith) (by exact_mod_cast hzX)
  have hcard : ((intervalSifted S X z).card:ℝ) ≤ X := Nat.cast_le.mpr (intervalSifted_card_le S X z)
  have hD : 2*K ≤ D := by
    dsimp [D]
    have hh : 0 ≤ C*K := mul_nonneg hC.le (by linarith only [hK])
    linarith only [hh,hK]
  by_cases hlarge : 512*Real.log 4 ≤ Real.log X
  · let Z := shiftedPrimeCutoff (Real.log X)
    have hZ := shiftedPrimeCutoff_bounds hlarge
    have hLX1 : 1 ≤ Real.log X := by nlinarith only [hlarge,hc]
    have hlogZ : Real.log X/K ≤ Real.log Z := hZ.2.1
    by_cases hSZ : S ≤ Z
    · let w := min z Z
      have hw : S ≤ w := le_min hSz hSZ
      have hw2 : 2 ≤ w := hS.trans hw
      have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
      have hwz : w ≤ z := min_le_left _ _
      have hwZ : w ≤ Z := min_le_right _ _
      have hscale : 4*Real.log 4*(2+Real.log w) ≤
          Real.log (Real.exp (Real.log X/4)) := by
        have hm := Real.log_le_log (by exact_mod_cast (show 0 < w by omega))
          (by exact_mod_cast hwZ : (w:ℝ) ≤ Z)
        have hh := shiftedPrimeCutoff_scale hlarge
        have hnon : 0 ≤ Real.log 4*(2+Real.log w) := by positivity
        nlinarith
      have hy : 1 < Real.exp (Real.log X/4) := Real.one_lt_exp_iff.mpr (by positivity)
      have hf := hbound S X w hS hw _ hy hscale
      have hlogw : Real.log z/K ≤ Real.log w := by
        rcases le_total z Z with hh|hh
        · have he : w=z := min_eq_left hh
          rw [he]
          exact div_le_self hlz.le hK
        · have he : w=Z := min_eq_right hh
          rw [he]
          exact (div_le_div_of_nonneg_right hlzX (by positivity)).trans hlogZ
      have hmain : C*X*Real.log S/Real.log w ≤ C*K*X*Real.log S/Real.log z := by
        have hh := div_le_div_of_nonneg_left
          (show 0 ≤ C*X*Real.log S by positivity) (by positivity : 0 < Real.log z/K) hlogw
        calc
          _ ≤ C*X*Real.log S/(Real.log z/K) := hh
          _ = _ := by field_simp
      have herr := shiftedPrimeCutoff_error hlarge
      rw [Real.exp_log (by linarith : (0:ℝ)<X)] at herr
      have herr' : 2*(Real.exp (Real.log X/4))^3 ≤ 96*(X:ℝ)/(Real.log X)^2 := by
        have hnon : (0:ℝ) ≤ shiftedPrimeCutoff (Real.log X) := Nat.cast_nonneg _
        linarith
      have hfrac : (X:ℝ)/(Real.log X)^2 ≤ 2*X*Real.log S/Real.log z := by
        have hnum : Real.log z ≤ 2*Real.log S*(Real.log X)^2 := by
          have hsq : Real.log X ≤ (Real.log X)^2 := by nlinarith
          nlinarith [sq_nonneg (Real.log X)]
        apply (div_le_div_iff₀ (sq_pos_of_pos hLX) hlz).mpr
        have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
        nlinarith
      have herror : 2*(Real.exp (Real.log X/4))^3 ≤ 192*X*Real.log S/Real.log z := by
        have hh := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ) ≤ 96)
        apply herr'.trans
        first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
      have hsub : ((intervalSifted S X z).card:ℝ) ≤ (intervalSifted S X w).card :=
        Nat.cast_le.mpr (Finset.card_le_card (intervalSifted_antitone hwz))
      have hfin := hsub.trans (hf.trans (add_le_add hmain herror))
      have hcoef : C*K+192 ≤ D := by dsimp [D]; linarith only [hK]
      have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (X:ℝ)*Real.log S/Real.log z by positivity)
      calc
        _ ≤ (C*K+192)*X*Real.log S/Real.log z := by
          convert hfin using 1 <;> first | rfl | ring
        _ ≤ _ := by convert hm using 1 <;> first | (with_reducible_and_instances rfl) | ring
    · have hlogS : Real.log X/K ≤ Real.log S := by
        exact hlogZ.trans (Real.log_le_log (by exact_mod_cast (show 0 < Z by omega))
          (by exact_mod_cast (show Z ≤ S by omega)))
      have hnum : Real.log z ≤ D*Real.log S := by
        have hh := (div_le_iff₀ (by positivity : 0<K)).mp hlogS
        have hDK : K ≤ D := by linarith
        have hm := mul_le_mul_of_nonneg_right hDK hlS.le
        linarith only [hh,hm,hlzX]
      apply hcard.trans
      apply (le_div_iff₀ hlz).mpr
      have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
      convert hh using 1 <;> first | rfl | ring
  · have hnum : Real.log z ≤ D*Real.log S := by
      have hl : Real.log X ≤ 2*K := by dsimp [K] <;> linarith
      have hD' : 4*K ≤ D := by
        dsimp [D]
        have hh : 0 ≤ C*K := mul_nonneg hC.le (by linarith only [hK])
        linarith only [hh]
      nlinarith only [hlzX,hl,hD',hSl,hK]
    apply hcard.trans
    apply (le_div_iff₀ hlz).mpr
    have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
    convert hh using 1 <;> first | rfl | ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalPartQuotient
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the complete interval part leaves an integer sifted by that interval. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_idempotent (n : ℕ) (U V : ℝ) :
    partBetween (partBetween n U V) U V = partBetween n U V := by
  have he : (partBetween n U V).primeFactorsList.filter
      (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) = (partBetween n U V).primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true (partBetween_support n U V hp)
  rw [partBetween,he,Nat.prod_primeFactorsList (partBetween_pos n U V).ne']

lemma prime_dvd_partBetween {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    {U V : ℝ} (hU : U < (p:ℝ)) (hV : (p:ℝ) ≤ V) (hpn : p ∣ n) :
    p ∣ partBetween n U V := by
  apply Nat.dvd_of_mem_primeFactorsList
  apply (partBetween_factors n U V).mem_iff.mp
  apply List.mem_filter.mpr
  exact ⟨(Nat.mem_primeFactorsList_iff_dvd hn.ne' hp).mpr hpn,decide_eq_true ⟨hU,hV⟩⟩

lemma interval_part_quotient_avoids {n : ℕ} (hn : 0 < n) (U V : ℝ) :
    ∀ p : ℕ,p.Prime → U < (p:ℝ) → (p:ℝ) ≤ V → ¬ p ∣ n/partBetween n U V := by
  let m := partBetween n U V
  have hm : 0 < m := partBetween_pos n U V
  have hd : m ∣ n := partBetween_dvd hn.ne' U V
  have hq : 0 < n/m := Nat.div_pos (Nat.le_of_dvd hn hd) hm
  have he : m*(n/m)=n := Nat.mul_div_cancel' hd
  have hb := congrArg (fun r => partBetween r U V) he
  rw [partBetween_mul hm.ne' hq.ne',partBetween_idempotent] at hb
  have hone : partBetween (n/m) U V=1 := by
    have hh : m*partBetween (n/m) U V=m*1 := by simpa only [mul_one] using hb
    exact Nat.eq_of_mul_eq_mul_left hm hh
  intro p hp hU hV hpn
  have hpd := prime_dvd_partBetween hq hp hU hV hpn
  rw [hone] at hpd
  exact hp.not_dvd_one hpd

lemma interval_part_fiber_count {S X z m : ℕ} (hm : 0 < m) (hS : 2 ≤ S)
    (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ X ∧ partBetween n S z=m) :
    Q.card ≤ (intervalSifted S (X/m) z).card := by
  classical
  have hd (n : ℕ) (hn : n ∈ Q) : m ∣ n := by
    have hh := partBetween_dvd (hQ n hn).1.ne' S z
    rwa [(hQ n hn).2.2] at hh
  have hi : Set.InjOn (fun n : ℕ => n/m) (↑Q : Set ℕ) := by
    intro n hn r hr he
    have hn' := Nat.mul_div_cancel' (hd n hn)
    have hr' := Nat.mul_div_cancel' (hd r hr)
    dsimp only at he
    rw [he] at hn'
    exact hn'.symm.trans hr'
  have hs : Q.image (fun n => n/m) ⊆ intervalSifted S (X/m) z := by
    intro q hq
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
    have h := hQ n hn
    apply (mem_intervalSifted hS).mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h.1 (hd n hn)) hm,
      Nat.div_le_div_right h.2.1⟩,?_⟩
    have ha := interval_part_quotient_avoids h.1 (S:ℝ) (z:ℝ)
    rw [h.2.2] at ha
    intro p hp hSp hpz
    exact ha p hp (by exact_mod_cast hSp) (by exact_mod_cast hpz)
  rw [← Finset.card_image_of_injOn hi]
  exact Finset.card_le_card hs

theorem interval_part_fiber_bound : ∃ C : ℝ,0 < C ∧ ∀ S X z m : ℕ,
    0 < m → 2 ≤ S → S ≤ z → z ≤ X/m → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ partBetween n S z=m) →
    (Q.card:ℝ) ≤ C*(X:ℝ)/(m:ℝ)*Real.log S/Real.log z := by
  obtain ⟨C,hC,hbound⟩ := interval_avoidance_count
  refine ⟨C,hC,?_⟩
  intro S X z m hm hS hSz hz Q hQ
  have hlS : 0 ≤ Real.log S := Real.log_nonneg (by exact_mod_cast (show 1 ≤ S by omega))
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hdiv : ((X/m:ℕ):ℝ) ≤ (X:ℝ)/m := Nat.cast_div_le
  calc
    _ ≤ ((intervalSifted S (X/m) z).card:ℝ) := Nat.cast_le.mpr (interval_part_fiber_count hm hS Q hQ)
    _ ≤ C*(X/m:ℕ)*Real.log S/Real.log z := hbound S (X/m) z hS hSz hz
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hdiv hC.le
      have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hlS) hlz.le
      convert hh' using 1 <;> first | rfl | ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalPartCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting distinct values by their complete prime-interval parts. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem interval_part_count : ∃ C : ℝ,0 < C ∧ ∀ S X z : ℕ,
    2 ≤ S → S ≤ z → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ z*partBetween n S z ≤ X) →
    (Q.card:ℝ) ≤ (C*X*Real.log S/Real.log z)*
      ∑ d ∈ Q.image (fun n => partBetween n S z),(d:ℝ)⁻¹ := by
  classical
  obtain ⟨C,hC,hbound⟩ := interval_part_fiber_bound
  refine ⟨C,hC,?_⟩
  intro S X z hS hSz Q hQ
  let f := fun n => partBetween n (S:ℝ) (z:ℝ)
  have hmap : ∀ n ∈ Q,f n ∈ Q.image f := fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩
  have hf (d : ℕ) (hd : d ∈ Q.image f) :
      ((Q.filter (fun n => f n=d)).card:ℝ) ≤
      (C*X*Real.log S/Real.log z)*(d:ℝ)⁻¹ := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
    have hm : 0 < f n := partBetween_pos n S z
    have hz : z ≤ X/f n := (Nat.le_div_iff_mul_le hm).mpr (hQ n hn).2.2
    have hb := hbound S X z (f n) hm hS hSz hz (Q.filter (fun r => f r=f n)) (by
      intro r hr
      obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
      exact ⟨(hQ r hr).1,(hQ r hr).2.1,he⟩)
    convert hb using 1 <;> first | rfl | ring
  have he := Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at he
  calc
    _ = ∑ d ∈ Q.image f,((Q.filter (fun n => f n=d)).card:ℝ) := he.symm
    _ ≤ ∑ d ∈ Q.image f,(C*X*Real.log S/Real.log z)*(d:ℝ)⁻¹ := Finset.sum_le_sum hf
    _ = _ := by rw [← Finset.mul_sum]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBandPartition
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from adjacent prime-factor bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_split (n : ℕ) {U V W : ℝ} (hUV : U ≤ V) (hVW : V ≤ W) :
    partBetween n U V*partBetween n V W=partBetween n U W := by
  apply Nat.eq_of_mul_eq_mul_left (partBelow_pos n U)
  calc
    partBelow n U*(partBetween n U V*partBetween n V W) =
        (partBelow n U*partBetween n U V)*partBetween n V W := by ring
    _ = partBelow n V*partBetween n V W := by rw [partBelow_band_split n hUV]
    _ = partBelow n W := partBelow_band_split n hVW
    _ = _ := (partBelow_band_split n (hUV.trans hVW)).symm

lemma partBetween_self (n : ℕ) (U : ℝ) : partBetween n U U=1 := by
  have he : n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ U)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro p _
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_and]
    exact not_le_of_gt
  simp only [partBetween,he,List.prod_nil]

lemma descending_chain_zero (Y : ℕ → ℝ) (k : ℕ)
    (hY : ∀ j < k,Y (j+1) ≤ Y j) : Y k ≤ Y 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    exact (hY k (by omega)).trans (ih (fun j hj => hY j (by omega)))

lemma partBetween_adjacent_product (n : ℕ) (Y : ℕ → ℝ) (k : ℕ)
    (hY : ∀ j < k,Y (j+1) ≤ Y j) :
    (∏ j ∈ Finset.range k,partBetween n (Y (j+1)) (Y j))=partBetween n (Y k) (Y 0) := by
  induction k with
  | zero => simp [partBetween_self]
  | succ k ih =>
    have hk0 := descending_chain_zero Y k (fun j hj => hY j (by omega))
    rw [Finset.prod_range_succ,ih (fun j hj => hY j (by omega)),mul_comm]
    exact partBetween_split n (hY k (by omega)) hk0

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PartitionedBandMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-band parts satisfy the independent mass estimate used in Ford 4.1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem partitioned_squarefree_mass : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (Y : ℕ → ℝ) (c R : Fin k → ℝ),
    (∀ j < k,Y (j+1) ≤ Y j) → (∀ j < k,2 ≤ Y (j+1)) →
    (∀ j,1 ≤ c j) → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,Squarefree n ∧ partBetween n (Y k) (Y 0)=n ∧
      ∀ j : Fin k,R j ≤ (omegaIn n (Y (j.val+1)) (Y j.val):ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ Real.exp
      (∑ j : Fin k,(c j*(B (Y j.val)-B (Y (j.val+1))+D)-R j*Real.log (c j))) := by
  obtain ⟨D,hD,hbound⟩ := finite_squarefree_band_mass
  refine ⟨D,hD,?_⟩
  intro k Y c R hY hY2 hc Q hQ
  let f := fun n (j : Fin k) => partBetween n (Y (j.val+1)) (Y j.val)
  apply hbound k (fun j => Y (j.val+1)) (fun j => Y j.val) c R
    (fun j => hY2 j.val j.isLt) (fun j => hY j.val j.isLt) hc Q f
  · intro n hn
    dsimp [f]
    rw [Fin.prod_univ_eq_prod_range (fun j => partBetween n (Y (j+1)) (Y j)),
      partBetween_adjacent_product n Y k hY]
    exact (hQ n hn).2.1
  · intro n hn j
    have hsq := (hQ n hn).1
    refine ⟨hsq.squarefree_of_dvd (partBetween_dvd hsq.ne_zero _ _),?_,?_⟩
    · intro p hp
      exact partBetween_support n _ _ hp
    · dsimp [f]
      rw [partBetween_omega]
      exact (hQ n hn).2.2 j

/-- A concrete count of the values themselves. The hypotheses concern only
their interval parts, squarefreeness, and factor-count lower bounds. -/
theorem partitioned_band_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℝ) (c R : Fin k → ℝ),
    2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    (∀ j < k,Y (j+1) ≤ Y j) → (∀ j < k,2 ≤ Y (j+1)) →
    (∀ j,1 ≤ c j) → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ z*partBetween n S z ≤ X ∧
      Squarefree (partBetween n S z) ∧
      ∀ j : Fin k,R j ≤ (omegaIn (partBetween n S z) (Y (j.val+1)) (Y j.val):ℝ)) →
    (Q.card:ℝ) ≤ C*X*Real.log S/Real.log z * Real.exp
      (∑ j : Fin k,(c j*(B (Y j.val)-B (Y (j.val+1))+D)-R j*Real.log (c j))) := by
  obtain ⟨C,hC,hcount⟩ := interval_part_count
  obtain ⟨D,hD,hmass⟩ := partitioned_squarefree_mass
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y c R hS hSz hY0 hYk hY hY2 hc Q hQ
  let P := Q.image (fun n => partBetween n (S:ℝ) (z:ℝ))
  have hP (n : ℕ) (hn : n ∈ P) :
      Squarefree n ∧ partBetween n (Y k) (Y 0)=n ∧
      ∀ j : Fin k,R j ≤ (omegaIn n (Y (j.val+1)) (Y j.val):ℝ) := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    refine ⟨(hQ v hv).2.2.2.1,?_,(hQ v hv).2.2.2.2⟩
    rw [hYk,hY0,partBetween_idempotent]
  have hm := hmass k Y c R hY hY2 hc P hP
  have hn := hcount S X z hS hSz Q (fun n hn =>
    ⟨(hQ n hn).1,(hQ n hn).2.1,(hQ n hn).2.2.1⟩)
  have hcoeff : 0 ≤ C*X*Real.log S/Real.log z := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ S by omega)))
    · exact (Real.log_pos (by exact_mod_cast (show 1 < z by omega))).le
  exact hn.trans (mul_le_mul_of_nonneg_left hm hcoeff)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandValueCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A value count with the band restrictions supplied by actual normal preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma descending_nat_chain_le {Y : ℕ → ℕ} {k j : ℕ}
    (hY : ∀ i < k,Y (i+1) ≤ Y i) (hj : j ≤ k) : Y k ≤ Y j := by
  have hseg : ∀ t < k-j,(Y (j+t+1):ℝ) ≤ Y (j+t) := by
    intro t ht
    exact_mod_cast hY (j+t) (by omega)
  have hh := descending_chain_zero (fun t => (Y (j+t):ℝ)) (k-j) (by
    intro t ht
    simpa only [Nat.add_assoc] using hseg t ht)
  simp only [Nat.add_sub_of_le hj,Nat.add_zero] at hh
  exact_mod_cast hh

theorem normal_preimage_band_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℕ),2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    (∀ j < k,Y (j+1) ≤ Y j) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      z*partBetween v S z ≤ X ∧ SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
      ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*Real.log S/Real.log z * Real.exp (normalBandExponent S D k Y) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := partitioned_band_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y hS hSz hY0 hYk hY Q hQ
  let c := fun j : Fin k => ((j.val+2:ℕ):ℝ)
  let R := fun j : Fin k => c j*(B (Y j.val)-B (Y (j.val+1))-Real.sqrt (B S*B (Y j.val)))
  have hlow (j : ℕ) (hj : j ≤ k) : S ≤ Y j := by
    rw [← hYk]
    exact descending_nat_chain_le hY hj
  have hupp (j : ℕ) (hj : j ≤ k) : Y j ≤ z := by
    have hh := descending_chain_zero (fun i => (Y i:ℝ)) j (by
      intro i hi
      exact_mod_cast hY i (by omega))
    rw [hY0] at hh
    exact_mod_cast hh
  have hc (j : Fin k) : 1 ≤ c j := by dsimp [c]; norm_cast; omega
  have hh := hbound S X z k (fun j => (Y j:ℝ)) c R hS hSz
    (by exact_mod_cast hY0) (by exact_mod_cast hYk)
    (fun j hj => by exact_mod_cast hY j hj)
    (fun j hj => by exact_mod_cast hS.trans (hlow (j+1) (by omega))) hc Q (by
      intro v hv
      obtain ⟨n,hn,hφ,hvX,hpart,hsqv,hsqn,hnormal,hprefix⟩ := hQ v hv
      have hv0 : 0 < v := hφ ▸ Nat.totient_pos.mpr hn
      refine ⟨hv0,hvX,hpart,partBetween_squarefree hv0.ne' hsqv,?_⟩
      intro j
      have hsq : SquarefreeAbove n (Y j.val) := by
        intro p hp hpl
        exact hsqn p hp ((show (S:ℝ) ≤ Y j.val by exact_mod_cast hlow j.val (by omega)).trans_lt hpl)
      have hb := ford_normal_part_band_lower hn (by omega : 0 < j.val+2) (hprefix j).1
        (show (S:ℝ) ≤ Y (j.val+1) by exact_mod_cast hlow (j.val+1) (by omega))
        (hY j.val j.isLt) (show (Y j.val:ℝ) ≤ z by exact_mod_cast hupp j.val (by omega))
        (by simpa using (hprefix j).2) hsq hnormal
      rw [hφ] at hb
      exact hb)
  simpa only [normalBandExponent,c,R,Nat.cast_add,Nat.cast_ofNat] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandExponent
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping the upper-count exponent into Ford's renewal coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma countBandWeight_difference (j : ℕ) :
    countBandWeight (j+1)-countBandWeight j = -a j := by
  simp only [countBandWeight,a,Nat.cast_add,Nat.cast_one]
  ring

lemma count_band_telescope (v : ℕ → ℝ) (k : ℕ) :
    v k-v 0+(∑ j ∈ Finset.range k,countBandWeight (j+2)*(v j-v (j+1))) =
      -(∑ j ∈ Finset.range k,a (j+1)*v j)+(1-countBandWeight (k+1))*v k := by
  induction k with
  | zero => simp [countBandWeight]
  | succ k ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hd := congrArg (fun c : ℝ => c*v k) (countBandWeight_difference (k+1))
    simp only [Nat.add_assoc] at hd
    nlinarith only [ih,hd]

lemma normal_band_exponent_identity (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ)
    (hYS : Y k=S) :
    B S-B (Y 0)+normalBandExponent S D k Y =
      -(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y := by
  have hexp : normalBandExponent S D k Y =
      (∑ j ∈ Finset.range k,countBandWeight (j+2)*(B (Y j)-B (Y (j+1))))+
      normalBandError S D k Y := by
    unfold normalBandExponent normalBandError
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ((j+2:ℕ):ℝ)*(B (Y j)-B (Y (j+1))+D)-
        ((j+2:ℕ):ℝ)*(B (Y j)-B (Y (j+1))-Real.sqrt (B S*B (Y j)))*Real.log (j+2)),
      Finset.mul_sum,← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [countBandWeight,Nat.cast_add,Nat.cast_ofNat]
    ring
  have ht := count_band_telescope (fun j => B (Y j)) k
  rw [hYS] at ht
  rw [hexp]
  linarith only [ht]

lemma normal_band_count_scale {S z : ℕ} (hS : 2 ≤ S) (hz : 2 ≤ z)
    (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) (hY0 : Y 0=z) (hYS : Y k=S) :
    Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y) =
      Real.exp (-(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y) := by
  have hlS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  rw [← normal_band_exponent_identity S D k Y hYS,hY0,Real.exp_add,
    Real.exp_sub]
  simp only [B,Real.exp_log hlS,Real.exp_log hlz]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallIntervalPart
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval part in Ford 4.1 is small enough for the quotient sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma partBetween_le_partBelow (n : ℕ) {S F : ℝ} (hSF : S ≤ F) :
    partBetween n S F ≤ partBelow n F := by
  have hp := partBelow_pos n S
  have he := partBelow_band_split n hSF
  nlinarith

lemma interval_part_log_bound (n : ℕ) {S F K : ℝ} (hSF : S ≤ F) (hF : 1 ≤ F)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ K) :
    Real.log (partBetween n S F) ≤ K*Real.log F := by
  have hp : (0:ℝ) < partBetween n S F := by exact_mod_cast partBetween_pos n S F
  have hb : (partBetween n S F:ℝ) ≤ F^n.primeFactorsList.length :=
    (Nat.cast_le.mpr (partBetween_le_partBelow n hSF)).trans (partBelow_bound n hF)
  have hl := Real.log_le_log hp hb
  rw [Real.log_pow] at hl
  exact hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hF))

lemma interval_part_sieve_size {n S X z : ℕ} {K : ℝ}
    (hS : S ≤ z) (hz : 1 ≤ z) (hX : 0 < X)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ K)
    (hsize : (K+1)*Real.log z ≤ Real.log X) :
    z*partBetween n S z ≤ X := by
  have hz0 : (0:ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hp0 : (0:ℝ) < partBetween n S z := by exact_mod_cast partBetween_pos n S z
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hl := interval_part_log_bound n (S:=(S:ℝ)) (F:=(z:ℝ))
    (by exact_mod_cast hS) (by exact_mod_cast hz) hΩ
  have hprod : Real.log ((z:ℝ)*(partBetween n S z:ℝ)) ≤ Real.log X := by
    rw [Real.log_mul hz0.ne' hp0.ne']
    nlinarith only [hl,hsize]
  have hh := (Real.log_le_log_iff (mul_pos hz0 hp0) hX0).mp hprod
  exact_mod_cast hh

lemma ford_interval_part_sieve_size {n S X z : ℕ}
    (hS : S ≤ z) (hz : 1 ≤ z) (hBX : 1 ≤ B X)
    (hΩ : (n.primeFactorsList.length:ℝ) ≤ 5*B X)
    (hcut : Real.log z ≤ Real.log X/(20*B X)) (hX : 0 < X) :
    z*partBetween n S z ≤ X := by
  apply interval_part_sieve_size hS hz hX hΩ
  have hB : 0 < 20*B X := by positivity
  have hh := (le_div_iff₀ hB).mp hcut
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
  have hc : 5*B X+1 ≤ 20*B X := by linarith only [hBX]
  have hm := mul_le_mul_of_nonneg_right hc hzlog
  nlinarith only [hh,hm]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordNormalCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-value upper count, with the exponent in Ford's coefficient form. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem ford_normal_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℕ),2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    1 ≤ B X → Real.log z ≤ Real.log X/(20*B X) →
    (∀ j < k,Y (j+1) ≤ Y j) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
      ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*Real.exp
      (-(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := normal_preimage_band_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y hS hSz hY0 hYS hBX hcut hY Q hQ
  have hX : 0 < X := by
    by_contra! hh
    have hz : X=0 := Nat.eq_zero_of_le_zero hh
    subst X
    norm_num [B] at hBX
  have hb := hbound S X z k Y hS hSz hY0 hYS hY Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnormal,hprefix⟩ := hQ v hv
    exact ⟨n,hn,hφ,hvX,ford_interval_part_sieve_size hSz (by omega) hBX hΩ hcut hX,
      hsqv,hsqn,hnormal,hprefix⟩)
  have he := normal_band_count_scale hS (hS.trans hSz) D k Y hY0 hYS
  calc
    _ ≤ C*X*Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y) := hb
    _ = C*X*(Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y)) := by ring
    _ = _ := by rw [he]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandErrorBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite-dimensional bound for the normal-band counting error. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normal_band_error_bound {S k : ℕ} {D H : ℝ} {Y : ℕ → ℕ}
    (hD : 0 ≤ D) (hS : 0 ≤ B S) (_hH : 0 ≤ H)
    (hY : ∀ j < k,B (Y j) ≤ H) :
    normalBandError S D k Y ≤
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ((j+2:ℕ):ℝ) ≤ (k:ℝ)+2 := by
    have hh := Finset.mem_range.mp hj
    exact_mod_cast (show j+2 ≤ k+2 by omega)
  have hsum : (∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)) ≤ (k:ℝ)*(k+2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k,((k:ℝ)+2) := Finset.sum_le_sum hterm
      _ = _ := by simp <;> ring
  have herror (j : ℕ) (hj : j ∈ Finset.range k) :
      ((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j)) ≤
      ((k:ℝ)+2)^2*Real.sqrt (B S*H) := by
    have hj0 : (0:ℝ) ≤ (j+2:ℕ) := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log ((j+2:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j+2 by omega))
    have hlog : Real.log ((j+2:ℕ):ℝ) ≤ (k:ℝ)+2 := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < ((j+2:ℕ):ℝ) by positivity)
      linarith [hterm j hj]
    have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hY j (Finset.mem_range.mp hj)) hS)
    have hc : ((j+2:ℕ):ℝ)*Real.log ((j+2:ℕ):ℝ) ≤ ((k:ℝ)+2)^2 := by
      nlinarith [hterm j hj]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using mul_le_mul hc hsqrt (Real.sqrt_nonneg _) (sq_nonneg _)
  have hs : (∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j))) ≤
      (k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k,((k:ℝ)+2)^2*Real.sqrt (B S*H) := Finset.sum_le_sum herror
      _ = _ := by simp <;> ring
  simpa only [normalBandError,mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hsum hD) hs

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandUnionCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual normal-preimage count over a finite family of cutoff vectors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem normal_band_union_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X k : ℕ) (H T : ℝ) (P : Finset (ℕ → ℕ)),
    2 ≤ S → 0 ≤ B S → 1 ≤ B X → 0 ≤ H →
    (∀ Y ∈ P,S ≤ Y 0 ∧ Y k=S ∧ Real.log (Y 0) ≤ Real.log X/(20*B X) ∧
      (∀ j < k,Y (j+1) ≤ Y j) ∧ (∀ j < k,B (Y j) ≤ H) ∧
      T ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j)) →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,∃ Y ∈ P,NormalBandWitness S X k Y v) →
    (Q.card:ℝ) ≤ C*X*P.card*Real.exp (-T+(1-countBandWeight (k+1))*B S+
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := ford_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X k H T P hS hBS hBX hH hP Q hQ
  let F := fun Y : ℕ → ℕ => Q.filter (NormalBandWitness S X k Y)
  have hcover : Q ⊆ P.biUnion F := by
    intro v hv
    obtain ⟨Y,hY,hvY⟩ := hQ v hv
    exact Finset.mem_biUnion.mpr ⟨Y,hY,Finset.mem_filter.mpr ⟨hv,hvY⟩⟩
  have hF (Y : ℕ → ℕ) (hY : Y ∈ P) :
      ((F Y).card:ℝ) ≤ C*X*Real.exp (-T+(1-countBandWeight (k+1))*B S+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := by
    obtain ⟨hSY,hYS,hcut,hdesc,hHbound,hscore⟩ := hP Y hY
    have hc := hbound S X (Y 0) k Y hS hSY rfl hYS hBX hcut hdesc (F Y)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    have herr := normal_band_error_bound hD.le hBS hH hHbound
    have hexp : -(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y ≤
        -T+(1-countBandWeight (k+1))*B S+D*(k:ℝ)*(k+2)+
          (k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by linarith
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
  calc
    _ ≤ ((P.biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ Y ∈ P,((F Y).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (P.biUnion F).card ≤ ∑ Y ∈ P,(F Y).card)
    _ ≤ ∑ _Y ∈ P,C*X*Real.exp (-T+(1-countBandWeight (k+1))*B S+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := Finset.sum_le_sum hF
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul] <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionSlack
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative strict slack in the published comparison exponent. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_a_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, a j) = (n+1 : ℝ)*Real.log (n+1)-n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [a, Nat.cast_add, Nat.cast_one]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonErrorBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rounding and normality errors fit inside the strict-slack saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_a_le_square (b : ℕ) : (∑ j ∈ Finset.Icc 1 b, a j) ≤ (b : ℝ)^2 := by
  rw [sum_a_Icc]
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hl : Real.log (b+1 : ℝ) ≤ b := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < b+1)
  have hh := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ b+1 by positivity)
  nlinarith

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

lemma loglogCutoff_mono : Monotone loglogCutoff := by
  intro b c hbc
  exact Nat.floor_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hbc))

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

lemma loglogCutoff_lt_of_lt_B {b : ℝ} {p : ℕ} (hp : 1 < p) (hb : b < B p) :
    loglogCutoff b < p := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp
  have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hb)
  have hlog : 0 < Real.log p := Real.log_pos hpR
  rw [B,Real.exp_log hlog,Real.exp_log (by linarith : (0:ℝ)<p)] at he
  have hf : (loglogCutoff b:ℝ) ≤ Real.exp (Real.exp b) := Nat.floor_le (Real.exp_pos _).le
  exact_mod_cast hf.trans_lt he

lemma loglog_grid_index_bounds {t : ℝ} (ht : 4 ≤ t) :
    let k := ⌊t⌋₊-1
    2 ≤ k ∧ (k:ℝ) < t ∧ t-2 < k := by
  have ht0 : 0 ≤ t := by linarith
  have hn4 : 4 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr ht
  have hn1 : 1 ≤ ⌊t⌋₊ := by omega
  dsimp only
  refine ⟨by omega,?_,?_⟩
  · rw [Nat.cast_sub hn1,Nat.cast_one]
    linarith [Nat.floor_le ht0]
  · rw [Nat.cast_sub hn1,Nat.cast_one]
    linarith [Nat.sub_one_lt_floor t]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CappedLoglogGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cap the log-log grid at the upper sieve endpoint. -/
noncomputable section
namespace TotientAsymptotic

lemma cappedLoglogIndex_mono (K : ℕ) : Monotone (cappedLoglogIndex K) := by
  intro t u htu
  exact min_le_min (Nat.sub_le_sub_right (Nat.floor_mono htu) 1) le_rfl

lemma cappedLoglogIndex_bounds {K : ℕ} {t U : ℝ} (hK : 2 ≤ K) (hKU : (K:ℝ) ≤ U)
    (ht : 4 ≤ t) (hU : t ≤ U) :
    2 ≤ cappedLoglogIndex K t ∧ cappedLoglogIndex K t ≤ K ∧
      (cappedLoglogIndex K t:ℝ) < t ∧ t-U+K-2 ≤ cappedLoglogIndex K t := by
  have hj := loglog_grid_index_bounds ht
  refine ⟨le_min hj.1 hK,min_le_right _ _,?_,?_⟩
  · exact (by exact_mod_cast (min_le_left (⌊t⌋₊-1) K) :
      (cappedLoglogIndex K t:ℝ) ≤ (⌊t⌋₊-1:ℕ)).trans_lt hj.2.1
  · by_cases hk : K ≤ ⌊t⌋₊-1
    · rw [cappedLoglogIndex,min_eq_right hk]
      linarith
    · have hk' : ⌊t⌋₊-1 ≤ K := by omega
      rw [cappedLoglogIndex,min_eq_left hk']
      linarith [hj.2.2]

lemma capped_loglog_prime {K p : ℕ} {U : ℝ} (hK : 2 ≤ K)
    (hKU : (K:ℝ) ≤ U) (hp : 1 < p) (ht : 4 ≤ B p) (hU : B p ≤ U) :
    let j := cappedLoglogIndex K (B p)
    2 ≤ j ∧ j ≤ K ∧ loglogCutoff j < p ∧
      B p-U+K-3 ≤ B (loglogCutoff j) ∧ B (loglogCutoff j) ≤ K ∧
      Real.log (loglogCutoff j) ≤ Real.exp K := by
  have hj := cappedLoglogIndex_bounds hK hKU ht hU
  have hb := loglogCutoff_bounds (by exact_mod_cast hj.1 : (2:ℝ) ≤ cappedLoglogIndex K (B p))
  dsimp only
  refine ⟨hj.1,hj.2.1,loglogCutoff_lt_of_lt_B hp hj.2.2.1,?_,?_,?_⟩
  · linarith only [hj.2.2.2,hb.2.1]
  · exact hb.2.2.1.trans (by exact_mod_cast hj.2.1)
  · exact hb.2.2.2.trans (Real.exp_le_exp.mpr (by exact_mod_cast hj.2.1))

lemma cappedLoglogIndex_lower {K L : ℕ} {t : ℝ} (hLK : L ≤ K)
    (hLt : (L:ℝ)+1 ≤ t) : L ≤ cappedLoglogIndex K t := by
  apply le_min _ hLK
  have hfloor : L+1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast hLt)
  omega

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCoordinateBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete bounds and nondegeneracy of the two coordinates in the bootstrap. -/
noncomputable section
namespace TotientAsymptotic

lemma prime_preimage_B_bound {x : ℝ} {n p : ℕ} (hx : 2 ≤ x)
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hφ : (n.totient:ℝ) ≤ x) :
    B p ≤ B x+2 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hφ0 : (0:ℝ) ≤ n.totient := Nat.cast_nonneg _
  have hnR : (n:ℝ) ≤ 2*x^2 := by
    have hn2 : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    exact hn2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0 hφ 2) (by norm_num))
  have hpR : (p:ℝ) ≤ 2*x^2 := (Nat.cast_le.mpr (Nat.le_of_dvd hn hpn)).trans hnR
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<p) hpR
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero _ hx0.ne'),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlog2 : Real.log (2:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hthree : Real.log p ≤ 3*Real.log x := by linarith
  have hh := Real.log_le_log (Real.log_pos hp1) hthree
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hlx.ne'] at hh
  have hl3 : Real.log (3:ℝ) ≤ 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num at ht
    exact ht
  exact hh.trans (by dsimp [B] <;> linarith)

lemma ford_coordinate_upper {x : ℝ} {n : ℕ} (hx : 4 ≤ x)
    (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x) (i : ℕ) :
    fordPrimeCoordinate n i ≤ B x+2 := by
  have hBx : 0 ≤ B x := by
    have hh : B 4 ≤ B x := Real.log_le_log (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hx)
    have h4 : 0 < B 4 := by
      unfold B
      apply Real.log_pos
      rw [Real.log_four_eq]
      linarith [Real.log_two_gt_d9]
    exact h4.le.trans hh
  by_cases hi : i < n.primeFactorsList.length
  · have hp := fordPrime_prime hi
    have hmem : fordPrime n i ∈ n.primeFactorsList := by
      rw [fordPrime_eq_get hi]
      exact List.mem_reverse.mp (List.getElem_mem _)
    have hb := prime_preimage_B_bound (by linarith) hn hp (Nat.dvd_of_mem_primeFactorsList hmem) hφ
    exact max_le (by linarith) hb
  · have he : fordPrime n i=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ThirdPrimeSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the two-coordinate exception has a small third prime. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_coordinate_antitone (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    fordPrimeCoordinate n j ≤ fordPrimeCoordinate n i := by
  by_cases hj : j < n.primeFactorsList.length
  · have hi : i < n.primeFactorsList.length := by omega
    have hp := fordPrime_prime hj
    have horder := fordPrime_antitone hi hj hij
    have hB : primeDoubleLog n j ≤ primeDoubleLog n i :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast hp.one_lt))
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast horder))
    exact max_le_max le_rfl hB
  · have he : fordPrime n j=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateActivePrefix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split an ordered coordinate vector at its last coordinate above a threshold. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma coordinate_active_prefix_bounds (n k : ℕ) (u : ℝ) :
    coordinateActivePrefix n k u ≤ k ∧
    (∀ j,1 ≤ j → j ≤ coordinateActivePrefix n k u → u < fordPrimeCoordinate n j) ∧
    (∀ j,coordinateActivePrefix n k u < j → j ≤ k → fordPrimeCoordinate n j ≤ u) := by
  classical
  let r := coordinateActivePrefix n k u
  have hr : r ≤ k := Nat.findGreatest_le k
  refine ⟨hr,?_,?_⟩
  · intro j hj hjr
    have hr0 : r ≠ 0 := by omega
    have hpr : u < fordPrimeCoordinate n r := (Nat.findGreatest_eq_iff.mp rfl).2.1 hr0
    exact hpr.trans_le (ford_coordinate_antitone n hjr)
  · intro j hrj hjk
    have hh := Nat.findGreatest_is_greatest hrj hjk
    exact le_of_not_gt hh

lemma sum_a_range_eq_Icc (k : ℕ) :
    (∑ j ∈ Finset.range k,a (j+1)) = ∑ j ∈ Finset.Icc 1 k,a j := by
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hj; omega⟩
  · intro i hi j hj he
    omega
  · intro j hj
    have hh := Finset.mem_Icc.mp hj
    exact ⟨j-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro j hj
    rfl

lemma sum_a_fin_le_square (k : ℕ) : (∑ j : Fin k,a (j.val+1)) ≤ (k:ℝ)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)),sum_a_range_eq_Icc]
  exact sum_a_le_square k

lemma coordinate_score_tail_le (n k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      (∑ j ∈ Finset.range (coordinateActivePrefix n k u),a (j+1)*fordPrimeCoordinate n (j+1))+
      u*(k:ℝ)^2 := by
  let r := coordinateActivePrefix n k u
  obtain ⟨hr,hlo,hhi⟩ := coordinate_active_prefix_bounds n k u
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => a (j+1)*fordPrimeCoordinate n (j+1)) hr
  have htail : (∑ j ∈ Finset.Ico r k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      u*(∑ j ∈ Finset.Icc 1 k,a j) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico r k,u*a (j+1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hm := Finset.mem_Ico.mp hj
        have ha := a_pos (show 1 ≤ j+1 by omega)
        have hc := hhi (j+1) (by omega) (by omega)
        nlinarith only [mul_le_mul_of_nonneg_left hc ha.le]
      _ = u*(∑ j ∈ Finset.Ico r k,a (j+1)) := by rw [Finset.mul_sum]
      _ ≤ u*(∑ j ∈ Finset.range k,a (j+1)) := by
        apply mul_le_mul_of_nonneg_left _ hu
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
        · intro j hj _
          exact (a_pos (by omega)).le
      _ = _ := by rw [sum_a_range_eq_Icc]
  have ha := mul_le_mul_of_nonneg_left (sum_a_le_square k) hu
  dsimp [r] at hsplit htail
  linarith

lemma coordinate_active_prefix_score {n k : ℕ} {L : ℕ} {T : ℝ}
    (hL : 3 ≤ L) (hT : ((L:ℝ)+1)*(k:ℝ)^2 < T)
    (hscore : T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) :
    ∃ r : ℕ,0 < r ∧ r ≤ k ∧
      (∀ j : Fin r,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
      T-((L:ℝ)+1)*(k:ℝ)^2 ≤ ∑ j : Fin r,a (j.val+1)*fordPrimeCoordinate n (j.val+1) := by
  let r := coordinateActivePrefix n k ((L:ℝ)+1)
  obtain ⟨hr,hlo,_⟩ := coordinate_active_prefix_bounds n k ((L:ℝ)+1)
  have hu : 0 ≤ (L:ℝ)+1 := by positivity
  have ht := coordinate_score_tail_le n k hu
  have hs : T ≤ ∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1) := by
    simpa only [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)*fordPrimeCoordinate n (j+1))] using hscore
  have hr0 : 0 < r := by
    by_contra hh
    have he : r=0 := by omega
    change (∑ j ∈ Finset.range k,a (j+1)*fordPrimeCoordinate n (j+1)) ≤
      (∑ j ∈ Finset.range r,a (j+1)*fordPrimeCoordinate n (j+1))+((L:ℝ)+1)*(k:ℝ)^2 at ht
    rw [he,Finset.sum_range_zero,zero_add] at ht
    linarith
  refine ⟨r,hr0,hr,?_,?_⟩
  · intro j
    have hh := hlo (j.val+1) (by omega) (by have := j.isLt; omega)
    have hcoord : 0 < fordPrimeCoordinate n (j.val+1) := by
      have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
      linarith
    rw [fordPrimeCoordinate_eq_raw_of_pos hcoord] at hh
    exact hh.le
  · rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a (j+1)*fordPrimeCoordinate n (j+1))]
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PositiveCoordinateGrid
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous finite-grid rounding of all positive ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma positive_coordinate_grid {x : ℝ} {n k K L : ℕ}
    (hx : 4 ≤ x) (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x)
    (hL : 3 ≤ L) (hLK : L ≤ K) (hK : (K:ℝ) ≤ B x+2)
    (hpositive : ∀ j : Fin k,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) :
    let g := coordinateGridIndex K n k
    (∀ j : Fin k,L ≤ g j ∧ g j ≤ K ∧
      loglogCutoff (g j) < fordPrime n (j.val+1) ∧
      B (loglogCutoff (g j)) ≤ K ∧
      Real.log (loglogCutoff (g j)) ≤ Real.exp K ∧
      j.val+2 ≤ n.primeFactorsList.length) ∧
    (∀ i j : Fin k,i ≤ j → g j ≤ g i) ∧
    (∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1))-
      (B x+5-K)*(∑ j : Fin k,a (j.val+1)) ≤
      ∑ j : Fin k,a (j.val+1)*B (loglogCutoff (g j)) := by
  let g := coordinateGridIndex K n k
  have hraw (j : Fin k) : 4 ≤ B (fordPrime n (j.val+1)) := by
    have hh : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hpositive j]
  have hidx (j : Fin k) : j.val+1 < n.primeFactorsList.length :=
    fordPrime_index_of_doubleLog_pos (lt_of_lt_of_le (by norm_num) (hraw j))
  have hc (j : Fin k) : fordPrimeCoordinate n (j.val+1)=B (fordPrime n (j.val+1)) :=
    max_eq_right (by change 0 ≤ B (fordPrime n (j.val+1)); linarith [hraw j])
  have hb (j : Fin k) : B (fordPrime n (j.val+1)) ≤ B x+2 := by
    rw [← hc j]
    exact ford_coordinate_upper hx hn hφ _
  have hg (j : Fin k) := capped_loglog_prime (show 2 ≤ K by omega) hK
    (fordPrime_prime (hidx j)).one_lt (hraw j) (hb j)
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ⟨cappedLoglogIndex_lower hLK (hpositive j),(hg j).2.1,(hg j).2.2.1,
      (hg j).2.2.2.2.1,(hg j).2.2.2.2.2,by have := hidx j; omega⟩
  · intro i j hij
    apply cappedLoglogIndex_mono K
    have hh := ford_coordinate_antitone n (show i.val+1 ≤ j.val+1 by exact Nat.add_le_add_right hij 1)
    rwa [hc i,hc j] at hh
  · have hterm (j : Fin k) :
        a (j.val+1)*fordPrimeCoordinate n (j.val+1)-(B x+5-K)*a (j.val+1) ≤
        a (j.val+1)*B (loglogCutoff (g j)) := by
      have hh := mul_le_mul_of_nonneg_left (hg j).2.2.2.1 (a_pos (show 0 < j.val+1 by omega)).le
      rw [hc j]
      dsimp [g,coordinateGridIndex]
      nlinarith only [hh]
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (j : Fin k) _ => hterm j)
    simpa only [Finset.sum_sub_distrib,← Finset.mul_sum] using hs

lemma coordinate_grid_cutoff_terminal (L k : ℕ) (g : Fin k → ℕ) :
    coordinateGridCutoff L k g k=loglogCutoff L := by simp [coordinateGridCutoff]

lemma coordinate_grid_cutoff_descending {L k : ℕ} {g : Fin k → ℕ}
    (hL : ∀ j,L ≤ g j) (hmono : ∀ i j : Fin k,i ≤ j → g j ≤ g i) :
    ∀ j < k,coordinateGridCutoff L k g (j+1) ≤ coordinateGridCutoff L k g j := by
  intro j hj
  by_cases hj1 : j+1 < k
  · simp only [coordinateGridCutoff,hj,hj1,dite_eq_left]
    exact loglogCutoff_mono (by exact_mod_cast hmono ⟨j,hj⟩ ⟨j+1,hj1⟩ (by simp))
  · simp only [coordinateGridCutoff,hj,hj1,dite_eq_left]
    exact loglogCutoff_mono (by exact_mod_cast hL ⟨j,hj⟩)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PositiveGridCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-grid counting for all positive ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem positive_grid_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ X k K L : ℕ,4 ≤ X → 1 ≤ B X → 0 < k → 3 ≤ L → L ≤ K →
    (K:ℝ) ≤ B X+2 → Real.exp K ≤ Real.log X/(20*B X) → ∀ T : ℝ,
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
      (∀ j : Fin k,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
      T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*(K+1:ℕ)^k*Real.exp
      (-T+(B X+5-K)*(∑ j : Fin k,a (j.val+1))+
        (1-countBandWeight (k+1))*B (loglogCutoff L)+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B (loglogCutoff L)*K)) := by
  classical
  obtain ⟨C,D,hC,hD,hunion⟩ := normal_band_union_count
  refine ⟨C,D,hC,hD,?_⟩
  intro X k K L hX hBX hk hL hLK hK hbudget T Q hQ
  let S := loglogCutoff L
  let U := T-(B X+5-K)*(∑ j : Fin k,a (j.val+1))
  let V : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ => Finset.range (K+1))
  let P0 := V.image (coordinateGridCutoff L k)
  let P := P0.filter (fun Y => S ≤ Y 0 ∧ Y k=S ∧
    Real.log (Y 0) ≤ Real.log X/(20*B X) ∧
    (∀ j < k,Y (j+1) ≤ Y j) ∧ (∀ j < k,B (Y j) ≤ K) ∧
    U ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j))
  have hcut := loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
  have hS : 2 ≤ S := hcut.1
  have hBS : 0 ≤ B S := by
    have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hcut.2.1]
  have hcover : ∀ v ∈ Q,∃ Y ∈ P,NormalBandWitness S X k Y v := by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hpos,hscore⟩ := hQ v hv
    let g := coordinateGridIndex K n k
    let Y := coordinateGridCutoff L k g
    obtain ⟨hg,hmono,hgrid⟩ := positive_coordinate_grid (by exact_mod_cast hX) hn
      (by exact_mod_cast (hφ ▸ hvX)) hL hLK hK hpos
    have hgm (j : Fin k) : L ≤ g j ∧ g j ≤ K ∧
        loglogCutoff (g j) < fordPrime n (j.val+1) ∧
        B (loglogCutoff (g j)) ≤ K ∧
        Real.log (loglogCutoff (g j)) ≤ Real.exp K ∧
        j.val+2 ≤ n.primeFactorsList.length := hg j
    have hYj (j : Fin k) : Y j.val=loglogCutoff (g j) := by simp [Y,coordinateGridCutoff]
    have hYscore : U ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j) := by
      have he : (∑ j ∈ Finset.range k,a (j+1)*B (Y j))=
          ∑ j : Fin k,a (j.val+1)*B (loglogCutoff (g j)) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        rw [hYj j]
      rw [he]
      dsimp [U]
      linarith
    have hYmem : Y ∈ P := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨g,Fintype.mem_piFinset.mpr
          (fun j => Finset.mem_range.mpr (by have := (hgm j).2.1; omega)),rfl⟩
      · have hY0 := hYj ⟨0,hk⟩
        refine ⟨?_,coordinate_grid_cutoff_terminal L k g,?_,?_,?_,hYscore⟩
        · rw [hY0]
          exact loglogCutoff_mono (by exact_mod_cast (hgm ⟨0,hk⟩).1)
        · rw [hY0]
          exact (hgm ⟨0,hk⟩).2.2.2.2.1.trans hbudget
        · exact coordinate_grid_cutoff_descending (fun j => (hgm j).1) hmono
        · intro j hj
          rw [hYj ⟨j,hj⟩]
          exact (hgm ⟨j,hj⟩).2.2.2.1
    refine ⟨Y,hYmem,n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,?_⟩
    intro j
    rw [hYj j]
    exact ⟨(hgm j).2.2.2.2.2,(hgm j).2.2.1⟩
  have hb := hunion S X k K U P hS hBS hBX (Nat.cast_nonneg K)
    (fun Y hY => (Finset.mem_filter.mp hY).2) Q hcover
  have hcard : (P.card:ℝ) ≤ (K+1:ℕ)^k := by
    have hc : P.card ≤ (K+1)^k := by
      calc
        _ ≤ P0.card := Finset.card_filter_le _ _
        _ ≤ V.card := Finset.card_image_le
        _ = _ := by simp [V,Fintype.card_piFinset]
    exact_mod_cast hc
  have hnon : 0 ≤ Real.exp (-U+(1-countBandWeight (k+1))*B S+
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*K)) := (Real.exp_pos _).le
  have hh := hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ C*X)) hnon)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  dsimp [U,S]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridExponentEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common error envelope when the active coordinate prefix varies in length. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma countBandWeight_lower (r : ℕ) : 1-countBandWeight (r+1) ≤ ((r:ℝ)+2)^2 := by
  have hl : Real.log ((r:ℝ)+1) ≤ r := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < (r:ℝ)+1 by positivity)
  have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ (r:ℝ)+1 by positivity)
  simp only [countBandWeight,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma grid_exponent_envelope {X r k K L : ℕ} {D T : ℝ}
    (hr : r ≤ k) (hD : 0 ≤ D) (hBS : 0 ≤ B (loglogCutoff L))
    (hK : (K:ℝ) ≤ B X+2) :
    -(T-((L:ℝ)+1)*(k:ℝ)^2)+(B X+5-K)*(∑ j : Fin r,a (j.val+1))+
      (1-countBandWeight (r+1))*B (loglogCutoff L)+D*(r:ℝ)*(r+2)+
        (r:ℝ)*(r+2)^2*Real.sqrt (B (loglogCutoff L)*K) ≤
    -T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
      D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K) := by
  have hr0 : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hrk : (r:ℝ) ≤ k := Nat.cast_le.mpr hr
  have hcost : 0 ≤ B X+5-K := by linarith
  have hs : (∑ j : Fin r,a (j.val+1)) ≤ (k:ℝ)^2 :=
    (sum_a_fin_le_square r).trans (pow_le_pow_left₀ hr0 hrk 2)
  have hscore := mul_le_mul_of_nonneg_left hs hcost
  have hw : 1-countBandWeight (r+1) ≤ ((k:ℝ)+2)^2 :=
    (countBandWeight_lower r).trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hweight := mul_le_mul_of_nonneg_right hw hBS
  have hdd : (r:ℝ)*(r+2) ≤ ((k:ℝ)+2)^2 := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hdd hD
  have hrr : (r:ℝ)*(r+2)^2 ≤ ((k:ℝ)+2)^3 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ (r:ℝ)+2 by positivity) (show (r:ℝ)+2 ≤ (k:ℝ)+2 by linarith) 2
    have hh := mul_le_mul hp (show (r:ℝ) ≤ (k:ℝ)+2 by linarith) hr0 (sq_nonneg _)
    nlinarith only [hh]
  have hroot := mul_le_mul_of_nonneg_right hrr (Real.sqrt_nonneg (B (loglogCutoff L)*K))
  nlinarith only [hscore,hweight,hd,hroot]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullCoordinateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Count a weighted-coordinate violation, allowing all short and small-coordinate tails. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem full_coordinate_count_oai : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ X k K L : ℕ,4 ≤ X → 1 ≤ B X → 3 ≤ L → L ≤ K →
    (K:ℝ) ≤ B X+2 → Real.exp K ≤ Real.log X/(20*B X) →
    ∀ T : ℝ,((L:ℝ)+1)*(k:ℝ)^2 < T → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
      T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*k*(K+1:ℕ)^k*Real.exp
      (-T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
        D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
  classical
  obtain ⟨C,D,hC,hD,hcount⟩ := positive_grid_count
  refine ⟨C,D,hC,hD,?_⟩
  intro X k K L hX hBX hL hLK hK hbudget T hT Q hQ
  let U := T-((L:ℝ)+1)*(k:ℝ)^2
  let W := -T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
    D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)
  let F := fun r : ℕ => Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
    (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
    SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
    (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
    (∀ j : Fin r,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
    U ≤ ∑ j : Fin r,a (j.val+1)*fordPrimeCoordinate n (j.val+1))
  have hcover : Q ⊆ (Finset.Icc 1 k).biUnion F := by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hscore⟩ := hQ v hv
    obtain ⟨r,hr0,hr,hpositive,hprefix⟩ := coordinate_active_prefix_score hL hT hscore
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_Icc.mpr ⟨hr0,hr⟩,
      Finset.mem_filter.mpr ⟨hv,n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hpositive,hprefix⟩⟩
  have hBS : 0 ≤ B (loglogCutoff L) := by
    have hh := (loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))).2.1
    have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hF (r : ℕ) (hr : r ∈ Finset.Icc 1 k) :
      ((F r).card:ℝ) ≤ C*X*(K+1:ℕ)^k*Real.exp W := by
    obtain ⟨hr0,hrk⟩ := Finset.mem_Icc.mp hr
    have hh := hcount X r K L hX hBX hr0 hL hLK hK hbudget U (F r)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    have he := grid_exponent_envelope (T:=T) hrk hD.le hBS hK
    have hexp := Real.exp_le_exp.mpr he
    have hpow : (((K+1:ℕ)^r):ℝ) ≤ ((K+1:ℕ)^k:ℝ) :=
      by exact_mod_cast (Nat.pow_le_pow_right (n:=K+1) (by omega) hrk)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ C*X)
    · exact hexp
    · positivity
    · positivity
  calc
    _ ≤ (((Finset.Icc 1 k).biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ r ∈ Finset.Icc 1 k,((F r).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le :
      ((Finset.Icc 1 k).biUnion F).card ≤ ∑ r ∈ Finset.Icc 1 k,(F r).card)
    _ ≤ ∑ _r ∈ Finset.Icc 1 k,C*X*(K+1:ℕ)^k*Real.exp W := Finset.sum_le_sum hF
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc]; push_cast <;> ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.full_coordinate_count_oai := @OAI.TotientAsymptotic.full_coordinate_count_oai
