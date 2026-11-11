-- Prove2me | solution 1 for OAI.TotientAsymptotic.ppt_fixed_bad_coordinate_value_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:38:34.31372+00:00
-- url     : https://prove2.me/submissions/e6c87799-ef2f-4274-b5c9-3c58ec852fda

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
import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_fixed_coordinate_grid_bound
import Theorems.Thm_OAI_TotientAsymptotic_terminal_prefix_mass_count

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
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence, uniqueness and positivity of the renewal parameters. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma renewalSeries_rho : renewalSeries rho = 1 := rho_mem.2.2

lemma summable_moment :
    Summable (fun n : ℕ => (n+1 : ℝ) * a (n+1) * rho^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _))
    (fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg rho_pos.le _))
    (summable_index_geometric rho_pos.le rho_lt_one 2)
  have h := mul_le_mul_of_nonneg_left (a_le_index (j := n+1) (by omega))
    (show (0 : ℝ) ≤ n+1 by positivity)
  simpa [pow_two] using h

lemma gamma_pos : 0 < gamma := by
  apply inv_pos.mpr
  apply summable_moment.tsum_pos (i := 0)
  · intro n
    exact mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _)
  · simpa using mul_pos (a_pos (j := 1) le_rfl) rho_pos

lemma alpha_pos (s : ℝ) : 0 < alpha s := mul_pos lam_pos (Real.exp_pos _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Phase
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cofinal logarithmic phases and convergence of the coefficient approximants. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma self_sub_log_tendsto :
    Tendsto (fun t : ℝ => t - Real.log t) atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun t : ℝ => 1 - Real.log t / t) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hmul : Tendsto (fun t : ℝ => t * (1-Real.log t / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_pos zero_lt_one tendsto_id hone
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

lemma psi_tendsto : Tendsto psi atTop atTop := by
  exact (self_sub_log_tendsto.comp Real.tendsto_log_atTop).atTop_div_const lam_pos



lemma theta_eventually_mem : ∀ᶠ x : ℝ in atTop, theta x ∈ Set.Ico (0 : ℝ) 1 := by
  have hp : Tendsto (fun x => psi (B x)) atTop atTop :=
    psi_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hp.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (psi (B x))
    change psi (B x) - (⌊psi (B x)⌋₊ : ℕ) < 1
    linarith

end TotientAsymptotic

end

end OAI
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma rho_pow_eq_exp (j : ℕ) : rho^j = Real.exp (-lam * j) := by
  have hlog : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [mul_comm, ← hlog, Real.exp_nat_mul, Real.exp_log rho_pos]

lemma alpha_theta_eq {x : ℝ} (hB : 1 < B x) :
    alpha (theta x) = lam * (B x / Real.log (B x)) * rho^(m x) := by
  have hlog : 0 < Real.log (B x) := Real.log_pos hB
  have he : lam * theta x =
      (Real.log (B x) - Real.log (Real.log (B x))) - lam * m x := by
    unfold theta psi
    field_simp [lam_pos.ne']
  rw [alpha, he, Real.exp_sub, Real.exp_sub,
    Real.exp_log (zero_lt_one.trans hB), Real.exp_log hlog, rho_pow_eq_exp]
  rw [neg_mul, Real.exp_neg]
  ring

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma m_tendsto : Tendsto m atTop atTop :=
  tendsto_nat_floor_atTop.comp (psi_tendsto.comp B_tendsto)

lemma bandCenterRatio_tendsto : Tendsto bandCenterRatio atTop (nhds 1) := by
  have hlogB : Tendsto (fun x => Real.log (B x)) atTop atTop :=
    Real.tendsto_log_atTop.comp B_tendsto
  have hsmall : Tendsto (fun x => Real.log (Real.log (B x)) / Real.log (B x))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogB
  have hpsi : Tendsto (fun x => psi (B x) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh : Tendsto
        (fun x => (1 - Real.log (Real.log (B x)) / Real.log (B x)) / lam)
        atTop (nhds (1 / lam)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).div_const lam
    apply hh.congr'
    filter_upwards [hlogB.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    unfold psi
    field_simp [hx.ne', lam_pos.ne']
  have hfloor : Tendsto (fun x => (m x : ℝ) / psi (B x)) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp (psi_tendsto.comp B_tendsto)
  have hmratio : Tendsto (fun x => (m x : ℝ) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh := hfloor.mul hpsi
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [(psi_tendsto.comp B_tendsto).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    change 0 < psi (B x) at hx
    field_simp [hx.ne']
  have hlm : Tendsto (fun x => lam * ((m x : ℝ) / Real.log (B x)))
      atTop (nhds 1) := by
    simpa only [mul_one_div_cancel lam_pos.ne'] using hmratio.const_mul lam
  have hh := hlm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun x => Real.log (B x) / (lam * m x)) atTop (nhds 1)
  simpa only [inv_one, mul_inv_rev, inv_div, inv_inv, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBox
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unit-box prime sums. The conditional input is the one-dimensional Mertens
estimate displayed in the proof of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 3.1, p. 11: the reciprocal-shift sum over
`exp(exp(m-1)) ≤ p < exp(exp(m))` equals `1 + O(exp(-m))`.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitPrimeWeight_nonneg (m : ℕ) : 0 ≤ unitPrimeWeight m := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  exact inv_nonneg.mpr (by linarith)

lemma abs_prod_sub_one_le {ι : Type*} (I : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (he : ∀ i ∈ I, 0 ≤ e i)
    (herr : ∀ i ∈ I, |f i-1| ≤ e i) :
    |(∏ i ∈ I, f i)-1| ≤ (∏ i ∈ I, (1+e i))-1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hfI := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have heI := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have herrI := fun j hj => herr j (Finset.mem_insert_of_mem hj)
    have hrec := ih hfI heI herrI
    have hfprod := Finset.prod_nonneg hfI
    have hP : (∏ j ∈ I, f j) ≤ ∏ j ∈ I, (1+e j) := by
      have hh := (le_abs_self ((∏ j ∈ I, f j)-1)).trans hrec
      linarith
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc
      _ = |(∏ j ∈ I, f j)*(f i-1)+((∏ j ∈ I, f j)-1)| := by congr 1; ring
      _ ≤ |(∏ j ∈ I, f j)*(f i-1)|+|(∏ j ∈ I, f j)-1| := abs_add_le _ _
      _ ≤ (∏ j ∈ I, (1+e j))*e i+((∏ j ∈ I, (1+e j))-1) := by
        rw [abs_mul, abs_of_nonneg hfprod]
        exact add_le_add (mul_le_mul hP (herr i (Finset.mem_insert_self _ _))
          (abs_nonneg _) (Finset.prod_nonneg (fun j hj => by linarith [heI j hj]))) hrec
      _ = _ := by ring

lemma abs_prod_sub_one_le_exp {ι : Type*} (I : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (he : ∀ i ∈ I, 0 ≤ e i)
    (herr : ∀ i ∈ I, |f i-1| ≤ e i) :
    |(∏ i ∈ I, f i)-1| ≤ Real.exp (∑ i ∈ I, e i)-1 := by
  apply (abs_prod_sub_one_le I f e hf he herr).trans
  apply sub_le_sub_right
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [he i hi]
  · intro i hi
    simpa [add_comm] using Real.add_one_le_exp (e i)

/-- The relative error in a multidimensional unit box depends on the sum of
the one-dimensional errors, rather than directly on the number of coordinates. -/
theorem prime_unit_box_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (I : Finset ι) (m : ι → ℕ),
      (∀ i ∈ I, 1 ≤ m i) →
      |(∏ i ∈ I, unitPrimeWeight (m i))-1| ≤
        Real.exp (C*∑ i ∈ I, Real.exp (-(m i : ℝ)))-1 := by
  obtain ⟨C, hC, hc⟩ := hford
  refine ⟨C, hC, ?_⟩
  intro ι I m hm
  have hh := abs_prod_sub_one_le_exp I (fun i => unitPrimeWeight (m i))
    (fun i => C*Real.exp (-(m i : ℝ)))
    (fun i _ => unitPrimeWeight_nonneg _) (fun i _ => mul_nonneg hC.le (Real.exp_pos _).le)
    (fun i hi => hc (m i) (hm i hi))
  simpa only [Finset.mul_sum] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime mass of finite disjoint unions of unit boxes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitPrimeBox_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (unitPrimeBox m) (unitPrimeBox n) := by
  suffices ∀ m n : ℕ, m < n → Disjoint (unitPrimeBox m) (unitPrimeBox n) by
    rcases lt_or_gt_of_ne hmn with h | h
    · exact this m n h
    · exact (this n m h).symm
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hm := (Finset.mem_filter.mp hp).2.2.2
  have hn := (Finset.mem_filter.mp hq).2.2.1
  have hmnR : (m : ℝ) ≤ (n : ℝ)-1 := by
    have hh : (m : ℝ)+1 ≤ n := by exact_mod_cast (show m+1 ≤ n by omega)
    linarith
  have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hmnR)
  exact (not_lt_of_ge (hn.trans' hh)) hm

lemma reciprocalShiftWeight_nonneg {N : ℕ} (p : Fin N → ℕ) :
    0 ≤ reciprocalShiftWeight p := by unfold reciprocalShiftWeight; positivity

lemma prime_box_mass {N : ℕ} (m : Fin N → ℕ) :
    (∑ p ∈ primeBoxTuples m, reciprocalShiftWeight p) =
      ∏ i, unitPrimeWeight (m i) := by
  symm
  unfold unitPrimeWeight primeBoxTuples
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Fintype.mem_piFinset.mp hp
  unfold reciprocalShiftWeight
  rw [Nat.cast_prod, Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hpi := (Finset.mem_filter.mp (hp' i)).2.1.two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p i), Nat.cast_one]

lemma primeBoxTuples_disjoint {N : ℕ} {m n : Fin N → ℕ} (hmn : m ≠ n) :
    Disjoint (primeBoxTuples m) (primeBoxTuples n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (unitPrimeBox_disjoint hi)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq i)

lemma gridPrimeMass_eq {N : ℕ} (K : Finset (Fin N → ℕ)) :
    gridPrimeMass K = ∑ m ∈ K, ∏ i, unitPrimeWeight (m i) := by
  classical
  unfold gridPrimeMass gridPrimeTuples
  rw [Finset.sum_biUnion (fun m _ n _ hmn => primeBoxTuples_disjoint hmn)]
  exact Finset.sum_congr rfl (fun m _ => prime_box_mass m)

/-- A coordinate-dependent error budget avoids a dimension factor when the
lower band endpoints grow geometrically towards the front of the prefix. -/
theorem grid_prime_mass_error_of_sum (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (K : Finset (Fin N → ℕ)) (e : ℝ),
      (∀ m ∈ K, ∀ i, 1 ≤ m i) →
      (∀ m ∈ K, (∑ i, Real.exp (-(m i : ℝ))) ≤ e) →
      |gridPrimeMass K-K.card| ≤ K.card*(Real.exp (C*e)-1) := by
  obtain ⟨C, hC, hc⟩ := prime_unit_box_error hford
  refine ⟨C, hC, ?_⟩
  intro N K e hm he
  have herr (m) (hmem : m ∈ K) :
      |(∏ i, unitPrimeWeight (m i))-1| ≤ Real.exp (C*e)-1 := by
    apply (hc Finset.univ m (fun i _ => hm m hmem i)).trans
    exact sub_le_sub_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (he m hmem) hC.le)) 1
  rw [gridPrimeMass_eq]
  calc
    _ = |∑ m ∈ K, ((∏ i, unitPrimeWeight (m i))-1)| := by
      rw [Finset.sum_sub_distrib]; simp
    _ ≤ ∑ m ∈ K, |(∏ i, unitPrimeWeight (m i))-1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ K, (Real.exp (C*e)-1) := Finset.sum_le_sum herr
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric volumes of the same disjoint boxes used in the prime sum. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    MeasurableSet (unitGridCell m) := by
  exact MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Ico)

lemma volume_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    volume (unitGridCell m) = 1 := by
  unfold unitGridCell
  rw [Real.volume_pi_Ico]
  simp

lemma unitGridCell_disjoint {N : ℕ} {m n : Fin N → ℕ} (hmn : m ≠ n) :
    Disjoint (unitGridCell m) (unitGridCell n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Set.disjoint_left.mpr
  intro u hum hun
  have hm := hum i (Set.mem_univ _)
  have hn := hun i (Set.mem_univ _)
  rcases lt_or_gt_of_ne hi with hi | hi
  · have h : (m i : ℝ)+1 ≤ n i := by exact_mod_cast (show m i+1 ≤ n i by omega)
    linarith [hm.2, hn.1]
  · have h : (n i : ℝ)+1 ≤ m i := by exact_mod_cast (show n i+1 ≤ m i by omega)
    linarith [hn.2, hm.1]

lemma volume_gridRegion {N : ℕ} (K : Finset (Fin N → ℕ)) :
    volume (gridRegion K) = K.card := by
  unfold gridRegion
  rw [measure_biUnion_finset
    (fun m _ n _ hmn => unitGridCell_disjoint hmn)
    (fun m _ => measurableSet_unitGridCell m)]
  simp only [volume_unitGridCell, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma gridRegion_volume_real {N : ℕ} (K : Finset (Fin N → ℕ)) :
    (volume (gridRegion K)).toReal = K.card := by
  rw [volume_gridRegion]
  simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Normalization
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of totient counts and uniform coefficient asymptotics. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma g_pos (j : ℕ) : 0 < g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [g]
    | succ n =>
      rw [g]
      apply Finset.sum_pos'
      · intro d hd
        exact (mul_pos (a_pos (by omega)) (ih (n-d) (by omega))).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (a_pos (by omega)) (ih n (by omega))

lemma G_pos {x : ℝ} (hx : 0 < B x) (j : ℕ) : 0 < G x j := by
  unfold G
  apply div_pos (pow_pos hx _)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos j)
    (Finset.prod_pos (fun i _ => g_pos i))

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGeometry
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The triangular slack calculation underlying `lem:simplex` and
`eq:intersection-volume` in the manuscript. These are identities for the
actual renewal coefficients, with no volume or counting estimate assumed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma g_convolution {j : ℕ} (hj : 0 < j) :
    g j = ∑ i ∈ Finset.range j, g i * a (j-i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [g]
  apply Finset.sum_bij (fun d _ => n-d)
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    exact Finset.mem_range.mpr (by omega)
  · intro d hd e he hde
    have hd' := Finset.mem_range.mp hd
    have he' := Finset.mem_range.mp he
    omega
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    refine ⟨n-i, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    have he : n+1-(n-d) = d+1 := by omega
    rw [he, mul_comm]

lemma weighted_slack_identity (N : ℕ) (u : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N+1), g i * prefixSlack N u i = u 0 := by
  have inner (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        g j * u j - if j = 0 then u 0 else 0 := by
    have hsub : Finset.range j ⊆ Finset.range (N+1) :=
      Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hj))
    have he : (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        ∑ i ∈ Finset.range j, g i * (a (j-i) * u j) := by
      symm
      calc
        _ = ∑ i ∈ Finset.range j, if i < j then g i * (a (j-i) * u j) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ite_eq_left (Finset.mem_range.mp hi)]
        _ = _ := Finset.sum_subset hsub (by
          intro i _ hi
          rw [ite_eq_right (by simpa using hi)])
    rw [he]
    by_cases hj0 : j = 0
    · subst j
      simp [g]
    · rw [ite_eq_right hj0, sub_zero, g_convolution (Nat.pos_of_ne_zero hj0), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  simp only [prefixSlack, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have hs : (∑ i ∈ Finset.range (N+1),
      ∑ j ∈ Finset.range (N+1), g i * (if i < j then a (j-i)*u j else 0)) =
      ∑ j ∈ Finset.range (N+1), (g j * u j - if j = 0 then u 0 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [mul_ite, mul_zero] using inner j hj
  rw [hs, Finset.sum_sub_distrib]
  simp

lemma prefixLinear_preserves_volume (N : ℕ) :
    MeasureTheory.Measure.map (prefixLinear N) MeasureTheory.volume = MeasureTheory.volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [prefixLinear_det]; norm_num),
    prefixLinear_det]
  simp

lemma prefixLinear_apply (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    prefixLinear N u i = u i - ∑ j : Fin N,
      if i < j then a (j.val-i.val) * u j else 0 := by
  change (∑ j : Fin N, prefixMatrix N i j * u j) = _
  have he (j : Fin N) : prefixMatrix N i j * u j =
      (if j = i then u j else 0) -
        (if i < j then a (j.val-i.val) * u j else 0) := by
    by_cases hij : i = j
    · subst j
      simp [prefixMatrix]
    · by_cases hij' : i < j <;> simp [prefixMatrix, hij, Ne.symm hij, hij']
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp

lemma prefixLinear_vector (N : ℕ) (u : ℕ → ℝ) (i : Fin N) :
    prefixLinear N (prefixVector N u) i = prefixSlack N u (i.val+1) := by
  rw [prefixLinear_apply]
  unfold prefixSlack prefixVector
  rw [Finset.sum_range_succ']
  simp only [Fin.lt_def, not_lt_zero, ite_false, if_false, add_zero]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => if i.val < k then a (k-i.val) * u (k+1) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixSlack_zero (N : ℕ) (u : ℕ → ℝ) :
    prefixSlack N u 0 = u 0 - ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  unfold prefixSlack
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_lt_succ, ite_true, if_true, Nat.sub_zero, lt_self_iff_false, ite_false, if_false, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun k => a (k+1) * u (k+1))]

lemma weighted_prefix_vector (N : ℕ) (u : ℕ → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N (prefixVector N u) i =
      ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  have h := weighted_slack_identity N u
  rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range,
    prefixSlack_zero] at h
  have hg0 : g 0 = 1 := by simp [g]
  rw [hg0, one_mul] at h
  simp_rw [prefixLinear_vector]
  linarith

lemma prefixVector_extend (N : ℕ) (u : Fin N → ℝ) :
    prefixVector N (extendPrefix N u) = u := by
  funext i
  simp [prefixVector, extendPrefix]

lemma weighted_prefixLinear (N : ℕ) (u : Fin N → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N u i =
      ∑ i : Fin N, a (i.val+1) * u i := by
  have h := weighted_prefix_vector N (extendPrefix N u)
  simpa [prefixVector_extend, extendPrefix] using h

/-- The available slack is the top budget minus all weighted tail thresholds. -/
lemma prefixRegion_eq_simplex_preimage (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    prefixRegion N B C₀ C =
      (fun u => prefixLinear N u - C) ⁻¹'
        weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i) := by
  ext u
  simp only [prefixRegion, weightedSimplex, Set.mem_ofPred_eq, Set.mem_preimage,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, weighted_prefixLinear]
  constructor
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mpr (hlo i), sub_le_sub_right hsum _⟩
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mp (hlo i), (sub_le_sub_iff_right _).mp hsum⟩

lemma prefixAffine_preserves_volume (N : ℕ) (C : Fin N → ℝ) :
    MeasureTheory.MeasurePreserving (fun u => prefixLinear N u - C)
      MeasureTheory.volume MeasureTheory.volume := by
  have hlin : MeasureTheory.MeasurePreserving (prefixLinear N)
      MeasureTheory.volume MeasureTheory.volume :=
    ⟨(prefixLinear N).continuous_of_finiteDimensional.measurable,
      prefixLinear_preserves_volume N⟩
  simpa only [sub_eq_add_neg, Function.comp_def] using
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-C)).comp hlin

lemma measurableSet_weightedSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (weightedSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, g (i.val+1) * v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

/-- Exact reduction of the prefix volume, valid for every fixed tail threshold. -/
theorem volume_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasureTheory.volume (prefixRegion N B C₀ C) =
      MeasureTheory.volume
        (weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i)) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume N C).measure_preimage
    (measurableSet_weightedSimplex _ _).nullMeasurableSet

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CubeBoundary
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes meeting the boundary lie in explicit prefix-slack shells. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitGridCell_coordinate_distance {N : ℕ} {m : Fin N → ℕ}
    {u v : Fin N → ℝ} (hu : u ∈ unitGridCell m) (hv : v ∈ unitGridCell m) :
    ∀ i, |u i-v i| ≤ 1 := by
  intro i
  have hui := hu i (Set.mem_univ _)
  have hvi := hv i (Set.mem_univ _)
  exact abs_le.mpr ⟨by linarith [hui.1, hvi.2], by linarith [hui.2, hvi.1]⟩

lemma prefixLinear_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) (i : Fin N) :
    |prefixLinear N u i-prefixLinear N v i| ≤ ((N-i.val : ℕ) : ℝ)^2 := by
  have he : prefixLinear N u i-prefixLinear N v i =
      (u i-v i)-∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
    rw [prefixLinear_apply, prefixLinear_apply]
    have hs : (∑ j : Fin N, ((if i < j then a (j.val-i.val)*u j else 0)-
        (if i < j then a (j.val-i.val)*v j else 0))) =
        ∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
      have heach (j : Fin N) :
          ((if i < j then a (j.val-i.val)*u j else 0)-
            (if i < j then a (j.val-i.val)*v j else 0)) =
          if i < j then a (j.val-i.val)*(u j-v j) else 0 := by
        split_ifs <;> ring
      simp_rw [heach]
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    calc
      _ = (u i-v i)-((∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0)-
          ∑ j : Fin N, if i < j then a (j.val-i.val)*v j else 0) := by ring
      _ = _ := by rw [← Finset.sum_sub_distrib, hs]
  rw [he]
  have hcoef (j : Fin N) (hj : j ∈ Finset.Ioi i) :
      0 ≤ a (j.val-i.val) ∧ a (j.val-i.val) ≤ (N-i.val : ℕ) := by
    have hji : i < j := Finset.mem_Ioi.mp hj
    have hji' : i.val < j.val := hji
    refine ⟨(a_pos (by omega)).le, (a_le_index (by omega)).trans ?_⟩
    exact_mod_cast (show j.val-i.val ≤ N-i.val by omega)
  calc
    _ ≤ |u i-v i|+|∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j)| := by simpa using abs_sub_le (u i-v i) 0 (∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j))
    _ ≤ 1+∑ j ∈ Finset.Ioi i, |a (j.val-i.val)*(u j-v j)| :=
      add_le_add (hdist i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1+∑ _j ∈ Finset.Ioi i, ((N-i.val : ℕ) : ℝ) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hcoef j hj).1]
      exact (mul_le_of_le_one_right (hcoef j hj).1 (hdist j)).trans (hcoef j hj).2
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
      have hi : i.val < N := i.isLt
      have he : N-1-i.val = N-i.val-1 := by omega
      rw [he, Nat.cast_sub (by omega : 1 ≤ N-i.val), Nat.cast_one]
      have hn : (1 : ℝ) ≤ (N-i.val : ℕ) := by exact_mod_cast (show 1 ≤ N-i.val by omega)
      nlinarith

lemma prefixBudget_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) :
    |(∑ j, a (j.val+1)*u j)-(∑ j, a (j.val+1)*v j)| ≤ (N : ℝ)^2 := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |a (j.val+1)*u j-a (j.val+1)*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_pos (a_pos (by omega))]
      apply (mul_le_of_le_one_right (a_pos (by omega)).le (hdist j)).trans
      exact (a_le_index (by omega)).trans (by exact_mod_cast (show j.val+1 ≤ N by omega))
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary simplex volume used by the prefix mass calculation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_standardSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (standardSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_simplexSection (N : ℕ) (T : ℝ) :
    MeasurableSet (simplexSection N T) := by
  change MeasurableSet ({p : ℝ × (Fin N → ℝ) | p.1 ∈ Set.Icc 0 T} ∩
    ({p : ℝ × (Fin N → ℝ) | ∀ i, 0 ≤ p.2 i} ∩
      {p : ℝ × (Fin N → ℝ) | (∑ i, p.2 i) ≤ T-p.1}))
  apply MeasurableSet.inter (measurable_fst measurableSet_Icc)
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).measurableSet)
  · exact measurableSet_le (by fun_prop) (by fun_prop)

lemma standardSimplex_succ_preimage (N : ℕ) (T : ℝ) :
    standardSimplex (N+1) T =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0) ⁻¹'
        simplexSection N T := by
  ext u
  simp only [standardSimplex, simplexSection, Set.mem_preimage, Set.mem_ofPred_eq,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
    Fin.removeNth, Fin.succAbove_zero, Set.mem_Icc]
  simp only [Fin.sum_univ_succ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨⟨h0, hn⟩, hs⟩
    have hn' : 0 ≤ ∑ i : Fin N, u i.succ := Finset.sum_nonneg (fun i _ => hn i)
    exact ⟨⟨h0, by linarith⟩, ⟨hn, by linarith⟩⟩
  · rintro ⟨⟨h0, _⟩, hn, hs⟩
    exact ⟨⟨h0, hn⟩, by linarith⟩

lemma volume_standardSimplex_succ (N : ℕ) (T : ℝ) :
    volume (standardSimplex (N+1) T) =
      ∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x)) := by
  rw [standardSimplex_succ_preimage]
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0).measure_preimage
    (measurableSet_simplexSection N T).nullMeasurableSet]
  change (volume.prod volume) (simplexSection N T) = _
  rw [Measure.prod_apply (measurableSet_simplexSection N T)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Set.Icc 0 T
  · have hx' := hx
    simp only [Set.mem_Icc] at hx'
    simp [simplexSection, hx, hx'.1, hx'.2]
  · have hx' : ¬ (0 ≤ x ∧ x ≤ T) := hx
    simp [simplexSection, hx, hx']

lemma volume_standardSimplex_zero {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex 0 T) = 1 := by
  have he : standardSimplex 0 T = Set.univ := by
    ext u
    simp [standardSimplex, hT]
  rw [he]
  change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
  simp

lemma integral_simplex_power (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in Set.Icc 0 T, (T-x)^N / (N.factorial : ℝ)) =
      T^(N+1) / ((N+1).factorial : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^N)]
  simp only [sub_zero, sub_self]
  rw [integral_pow]
  simp only [zero_pow (by omega : N+1 ≠ 0), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_div]

theorem volume_standardSimplex (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex N T) = ENNReal.ofReal (T^N / (N.factorial : ℝ)) := by
  induction N generalizing T with
  | zero => simpa using volume_standardSimplex_zero hT
  | succ N ih =>
    rw [volume_standardSimplex_succ]
    have he : (∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x))) =
        ∫⁻ x in Set.Icc 0 T, ENNReal.ofReal ((T-x)^N / (N.factorial : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact ih (sub_nonneg.mpr hx.2)
    rw [he, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_simplex_power N hT]
    · exact (show Continuous (fun x : ℝ => (T-x)^N / (N.factorial : ℝ)) by
        fun_prop).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (Nat.cast_nonneg _)

lemma weightedScale_apply (N : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    weightedScale N v i = g (i.val+1) * v i := by
  simp [weightedScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma weightedScale_det (N : ℕ) :
    LinearMap.det (weightedScale N) = ∏ i : Fin N, g (i.val+1) := by
  rw [weightedScale, LinearMap.det_toLin', Matrix.det_diagonal]

lemma weightedScale_det_pos (N : ℕ) : 0 < LinearMap.det (weightedScale N) := by
  rw [weightedScale_det]
  exact Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))

lemma weightedSimplex_eq_preimage (N : ℕ) (T : ℝ) :
    weightedSimplex N T = weightedScale N ⁻¹' standardSimplex N T := by
  ext v
  simp only [weightedSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    weightedScale_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (g_pos _)).symm)
    Iff.rfl

lemma volume_weightedSimplex_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [weightedSimplex_eq_preimage, ← Measure.map_apply
    (weightedScale N).continuous_of_finiteDimensional.measurable
    (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (weightedScale_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    weightedScale_det, abs_inv, abs_of_pos (Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Finset.prod_nonneg (fun (i : Fin N) _ => (g_pos (i.val+1)).le)))]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma volume_weightedSimplex (N : ℕ) (hN : 0 < N) (T : ℝ) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal ((max T 0)^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  by_cases hT : 0 ≤ T
  · rw [max_eq_left hT]
    exact volume_weightedSimplex_nonneg N hT
  · have he : weightedSimplex N T = ∅ := by
      ext v
      simp only [weightedSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hv, hs⟩
      have hn : 0 ≤ ∑ i : Fin N, g (i.val+1) * v i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (g_pos _).le (hv i))
      linarith
    rw [he, measure_empty, max_eq_right (le_of_not_ge hT), zero_pow hN.ne', zero_div,
      ENNReal.ofReal_zero]

/-- The explicit determinant-one prefix volume formula from the manuscript. -/
theorem volume_prefixRegion_explicit (N : ℕ) (hN : 0 < N)
    (B C₀ : ℝ) (C : Fin N → ℝ) :
    volume (prefixRegion N B C₀ C) =
      ENNReal.ofReal ((max (B-C₀-∑ i : Fin N, g (i.val+1)*C i) 0)^N /
        ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [volume_prefixRegion, volume_weightedSimplex N hN]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexShell
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit slack-shell bounds for the prefix simplexes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasurableSet (prefixRegion N B C₀ C) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable (measurableSet_weightedSimplex _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConvolution
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The dominated convolution limit needed for the finite-tail volume asymptotic.
The sole published input here is Ford's bounded renewal error, Lemma 3.7 of
*The distribution of totients*, arXiv:1104.3264v2 (2013), with Ford's constant
lambda denoted by gamma in this development.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_properties (hford : FordRenewalInput) :
    Tendsto normalizedRenewal atTop (nhds gamma) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖normalizedRenewal n‖ ≤ K := by
  obtain ⟨C, hC, herr⟩ := hford
  have hb (n : ℕ) : |normalizedRenewal n-gamma| ≤ C*rho^n := by
    have he : normalizedRenewal n-gamma = (g n-gamma*(rho^n)⁻¹)*rho^n := by
      unfold normalizedRenewal
      field_simp [rho_pos.ne']
    rw [he, abs_mul, abs_of_pos (pow_pos rho_pos _)]
    exact mul_le_mul_of_nonneg_right (herr n) (pow_nonneg rho_pos.le _)
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun n => C*rho^n) (fun n => dist_nonneg) ?_ ?_
    · intro n
      simpa only [Real.dist_eq] using hb n
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  · refine ⟨gamma+C, add_nonneg gamma_pos.le hC, fun n => ?_⟩
    have hg : 0 ≤ normalizedRenewal n := mul_nonneg (g_pos n).le (pow_nonneg rho_pos.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hg]
    have hpow : rho^n ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
    have h := (abs_le.mp (hb n)).2
    nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailRenewal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-tail budget and its renewal-convolution limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma alpha_ge_lam {s : ℝ} (hs : 0 ≤ s) : lam ≤ alpha s := by
  unfold alpha
  have he : 1 ≤ Real.exp (lam*s) := Real.one_le_exp (mul_nonneg lam_pos.le hs)
  nlinarith [lam_pos]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Prefactor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-tail prefactor, including its dependence on the moving phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma sub_div_self_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => ((m x-k : ℕ) : ℝ)/(m x : ℝ)) atTop (nhds 1) := by
  have hi : Tendsto (fun x : ℝ => (m x : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp m_tendsto)
  have hh : Tendsto (fun x : ℝ => 1-(k : ℝ)*(m x : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (k : ℝ))
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hk hm
  rw [Nat.cast_sub hk]
  field_simp [show (m x : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

lemma normalized_prefactor_step (hford : FordRenewalInput) (k : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x) *
      (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)) atTop (nhds (gamma*rho^k)) := by
  have hn := (normalizedRenewal_properties hford).1.comp
    ((tendsto_sub_atTop_nat k).comp m_tendsto)
  have hh := (((sub_div_self_tendsto k).mul hn).mul_const (rho^k)).div
    bandCenterRatio_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hh
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hk hm
  have hpow : rho^(m x-k)*rho^k = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  change (((m x-k : ℕ) : ℝ)/(m x : ℝ) * normalizedRenewal (m x-k) * rho^k) /
      bandCenterRatio x = alpha (theta x) * (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)
  rw [alpha_theta_eq hB]
  unfold normalizedRenewal bandCenterRatio
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  field_simp [hmn, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']
  rw [← hpow]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous bound for all projected prefix volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma inverse_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    (m x : ℝ)/(B x*rho^(m x)) = (alpha (theta x)*bandCenterRatio x)⁻¹ := by
  rw [alpha_theta_eq hB]
  unfold bandCenterRatio
  field_simp [(Real.log_pos hB).ne', (zero_lt_one.trans hB).ne',
    lam_pos.ne', Nat.cast_ne_zero.mpr hm.ne', rho_pos.ne']

lemma inverse_scale_bound : ∀ᶠ x : ℝ in atTop,
    (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0),
    bandCenterRatio_tendsto.eventually
      (eventually_gt_nhds (show (1/2 : ℝ) < 1 by norm_num))] with x hx hB hm hv
  rw [inverse_scale_eq hB hm]
  have ha := alpha_ge_lam hx.1
  have hprod : lam/2 ≤ alpha (theta x)*bandCenterRatio x := by
    nlinarith [lam_pos, alpha_pos (theta x)]
  calc
    _ ≤ (lam/2)⁻¹ := inv_anti₀ (div_pos lam_pos (by norm_num)) hprod
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexScaling
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal normalization of the enlarged simplexes used by prime boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma simplexScale_apply {N : ℕ} (κ u : Fin N → ℝ) (i : Fin N) :
    simplexScale κ u i = u i/κ i := by
  simp [simplexScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

lemma simplexScale_det {N : ℕ} (κ : Fin N → ℝ) :
    LinearMap.det (simplexScale κ) = (∏ i, κ i)⁻¹ := by
  rw [simplexScale, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_inv_distrib]

lemma enlargedSimplex_mapsTo {N : ℕ} {B β₀ : ℝ} {β κ : Fin N → ℝ}
    (hβ₀ : 0 < β₀) (hβ : ∀ i, 0 < β i) (hκ : ∀ i, 0 < κ i)
    (htop : ∀ i, β₀ ≤ κ i) (hstep : ∀ i j, i < j → β i*κ i ≤ κ j) :
    Set.MapsTo (simplexScale κ) (enlargedSimplex N B β₀ β) (prefixRegion N B 0 0) := by
  intro u hu
  constructor
  · intro i
    rw [prefixLinear_apply, simplexScale_apply]
    simp only [simplexScale_apply]
    have hsum : (∑ j : Fin N, if i < j then a (j.val-i.val)*(u j/κ j) else 0) ≤
        (∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0)/(β i*κ i) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · have hnonneg := mul_nonneg (a_pos (j := j.val-i.val) (by have := hij; simp only [Fin.lt_def] at this; omega)).le (hu.1 j)
        calc
          _ = (a (j.val-i.val)*u j)/κ j := by ring
          _ ≤ _ := div_le_div_of_nonneg_left hnonneg (mul_pos (hβ i) (hκ i)) (hstep i j hij)
      · simp
    have hb := div_le_div_of_nonneg_right (hu.2.1 i) (mul_pos (hβ i) (hκ i)).le
    have he : (β i*u i)/(β i*κ i) = u i/κ i := by field_simp [(hβ i).ne', (hκ i).ne']
    rw [he] at hb
    have hh := hsum.trans hb
    change 0 ≤ u i/κ i-_
    linarith
  · simp only [simplexScale_apply, sub_zero]
    calc
      _ ≤ (∑ i : Fin N, a (i.val+1)*u i)/β₀ := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro i _
        calc
          _ = (a (i.val+1)*u i)/κ i := by ring
          _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (a_pos (by omega)).le (hu.1 i)) hβ₀ (htop i)
      _ ≤ (β₀*B)/β₀ := div_le_div_of_nonneg_right hu.2.2 hβ₀.le
      _ = B := by field_simp

lemma enlargementScale_pos {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    0 < enlargementScale β i :=
  Finset.prod_pos (fun r _ => lt_of_lt_of_le zero_lt_one (hβ r))

lemma enlargementScale_top {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    β 0 ≤ enlargementScale β i := by
  have hh : (∏ r ∈ Finset.range 1, β r) ≤ ∏ r ∈ Finset.range (i.val+1), β r := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono (by omega))
    · intro r _
      exact (zero_le_one.trans (hβ r))
    · intro r _ _
      exact hβ r
  simpa [enlargementScale] using hh

lemma enlargementScale_step {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r)
    (i j : Fin N) (hij : i < j) :
    β (i.val+1)*enlargementScale β i ≤ enlargementScale β j := by
  have hh : (∏ r ∈ Finset.range (i.val+2), β r) ≤ ∏ r ∈ Finset.range (j.val+1), β r := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono (by have := hij; simp only [Fin.lt_def] at this; omega))
    · intro r _
      exact (zero_le_one.trans (hβ r))
    · intro r _ _
      exact hβ r
  rw [show i.val+2=(i.val+1)+1 by omega, Finset.prod_range_succ] at hh
  simpa only [enlargementScale, mul_comm] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EnlargementCost
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Jacobian bounds for the enlarged full-dimensional simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma triangular_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, ∑ r ∈ Finset.range (i+1), f r) =
      ∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*f r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hs : (∑ r ∈ Finset.range N, ((N+1-r : ℕ) : ℝ)*f r) =
        (∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*f r)+∑ r ∈ Finset.range N, f r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have he : N+1-r=(N-r)+1 := by have := Finset.mem_range.mp hr; omega
      rw [he, Nat.cast_add, Nat.cast_one]
      ring
    rw [hs, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
    ring

lemma enlargementScale_le_exp {N : ℕ} {β : ℕ → ℝ}
    (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    enlargementScale β i ≤ Real.exp (∑ r ∈ Finset.range (i.val+1), (β r-1)) := by
  rw [enlargementScale, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro r _
    exact zero_le_one.trans (hβ r)
  · intro r _
    have hh := Real.add_one_le_exp (β r-1)
    linarith

/-- The accumulated Jacobian is controlled by the weighted perturbation sum. -/
theorem enlargement_jacobian_bound {N : ℕ} {β : ℕ → ℝ}
    (hβ : ∀ r, 1 ≤ β r) :
    (∏ i : Fin N, enlargementScale β i) ≤
      Real.exp (∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*(β r-1)) := by
  calc
    _ ≤ ∏ i : Fin N, Real.exp (∑ r ∈ Finset.range (i.val+1), (β r-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (enlargementScale_pos hβ i).le
      · intro i _
        exact enlargementScale_le_exp hβ i
    _ = Real.exp (∑ i : Fin N, ∑ r ∈ Finset.range (i.val+1), (β r-1)) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => ∑ r ∈ Finset.range (i+1), (β r-1)),
        triangular_sum]

/-- Perturbations indexed by distance from the top are charged only their
remaining dimension, and can therefore be bounded by one convergent tail. -/
lemma reverse_perturbation_sum_le {m P : ℕ} (hPm : P ≤ m) (e : ℕ → ℝ)
    (he : ∀ h, 0 ≤ e h) (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) :
    (∑ r ∈ Finset.range (m-P), ((m-P-r : ℕ) : ℝ)*e (m-r)) ≤
      ∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n) := by
  have hs : (∑ r ∈ Finset.range (m-P), ((m-P-r : ℕ) : ℝ)*e (m-r)) ≤
      ∑ r ∈ Finset.range (m-P), ((m-r : ℕ) : ℝ)*e (m-r) := by
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_right _ (he _)
    exact_mod_cast (show m-P-r ≤ m-r by omega)
  apply hs.trans
  have heq : (∑ r ∈ Finset.range (m-P), ((m-r : ℕ) : ℝ)*e (m-r)) =
      ∑ r ∈ Finset.range (m-P), ((P+1+r : ℕ) : ℝ)*e (P+1+r) := by
    apply Finset.sum_bij (fun r _ => m-P-1-r)
    · intro r hr
      have := Finset.mem_range.mp hr
      exact Finset.mem_range.mpr (by omega)
    · intro r hr s hs hrs
      have := Finset.mem_range.mp hr
      have := Finset.mem_range.mp hs
      omega
    · intro s hs
      have := Finset.mem_range.mp hs
      refine ⟨m-P-1-s, Finset.mem_range.mpr (by omega), ?_⟩
      omega
    · intro r hr
      have := Finset.mem_range.mp hr
      congr 2 <;> omega
  rw [heq]
  have hshift := hsum.comp_injective (show Function.Injective (fun n : ℕ => P+1+n) by
    intro a b h; exact Nat.add_left_cancel h)
  have htail := hsum.comp_injective (show Function.Injective (fun n : ℕ => P+n) by
    intro a b h; exact Nat.add_left_cancel h)
  apply (hshift.sum_le_tsum _ (fun n _ => mul_nonneg (Nat.cast_nonneg _) (he _))).trans
  have ht : (∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n)) =
      (P : ℝ)*e P + ∑' n : ℕ, ((P+1+n : ℕ) : ℝ)*e (P+1+n) := by
    simpa only [Function.comp_def, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
      htail.tsum_eq_zero_add
  rw [ht]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (he _))

/-- The actual reverse-indexed enlargement has a uniform full Jacobian. -/
theorem reverse_enlargement_jacobian {m P : ℕ} (hPm : P ≤ m)
    (e : ℕ → ℝ) (he : ∀ h, 0 ≤ e h)
    (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) :
    (∏ i : Fin (m-P), enlargementScale (fun r => 1+e (m-r)) i) ≤
      Real.exp (∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n)) := by
  apply (enlargement_jacobian_bound (fun r => by linarith [he (m-r)])).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  exact reverse_perturbation_sum_le hPm e he hsum

/-- Through the retained prefix, each individual scaling factor tends to one
with the prefix cutoff, even when the full dimension grows. -/
theorem reverse_enlargement_coordinate {m H N : ℕ} (hHm : H ≤ m)
    (e : ℕ → ℝ) (he : ∀ h, 0 ≤ e h)
    (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) (i : Fin N)
    (hi : i.val < m-H) :
    enlargementScale (fun r => 1+e (m-r)) i ≤
      Real.exp (∑' n : ℕ, ((H+n : ℕ) : ℝ)*e (H+n)) := by
  apply (enlargementScale_le_exp (fun r => by linarith [he (m-r)]) i).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  apply le_trans _ (reverse_perturbation_sum_le hHm e he hsum)
  calc
    _ ≤ ∑ r ∈ Finset.range (m-H), e (m-r) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro r _ _
      exact he _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      have hr1 : (1 : ℝ) ≤ (m-H-r : ℕ) := by
        exact_mod_cast (show 1 ≤ m-H-r by have := Finset.mem_range.mp hr; omega)
      exact le_mul_of_one_le_left (he _) hr1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EnlargementTail
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two perturbations used for full prime boxes have summable weighted
cost, including after multiplication by the smooth-cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma simplexBoxError_nonneg {C : ℝ} (hC : 0 ≤ C) (h : ℕ) :
    0 ≤ simplexBoxError C h := by
  unfold simplexBoxError
  exact add_nonneg (by positivity)
    (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (pow_nonneg rho_pos.le _))

lemma simplexBoxError_weighted (C : ℝ) (h : ℕ) :
    (h : ℝ)*simplexBoxError C h =
      (1/10000 : ℝ)*((h : ℝ)^1*(Real.exp (-(1/40 : ℝ)))^h)+
      C*((h : ℝ)^3*rho^h) := by
  unfold simplexBoxError
  ring

lemma summable_simplexBoxError_weighted (C : ℝ) :
    Summable (fun h : ℕ => (h : ℝ)*simplexBoxError C h) := by
  have hq : ‖Real.exp (-(1/40 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  simp_rw [simplexBoxError_weighted]
  exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 3 hr).mul_left _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RemainderSplit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the prime prefix from its discrete tail thresholds. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prefix_sum_fin {J i : ℕ} (u : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (i+1) J, a (r-i)*u r) =
      ∑ j : Fin J, if i < j.val+1 then a (j.val+1-i)*u (j.val+1) else 0 := by
  have hs : Finset.Icc (i+1) J = (Finset.Icc 1 J).filter (fun r => i < r) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hs, Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
  · intro j _ k _ he
    apply Fin.ext
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro j _
    rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassMajorant
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing over witnesses is an upper bound, including repeated tail primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma prod_fin_shifted {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∏ i : Fin N, f (i.val+1)) = ∏ r ∈ Finset.Icc 1 N, f r := by
  apply Finset.prod_bij (fun i _ => i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro r hr
    have := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro i _
    rfl

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBoxGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic prime boxes and their real double-logarithmic cells agree. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_unitPrimeBox_iff {p m : ℕ} :
    p ∈ unitPrimeBox m ↔ p.Prime ∧
      (m : ℝ)-1 ≤ Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) < m := by
  have hlog {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  constructor
  · intro hp
    obtain ⟨_, hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    refine ⟨hp, ?_, ?_⟩
    · have h1 := Real.log_le_log (Real.exp_pos _) hlo
      have h2 := Real.log_le_log (Real.exp_pos _) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
    · have h1 := Real.log_lt_log (by exact_mod_cast hp.pos) hhi
      have h2 := Real.log_lt_log (hlog hp) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
  · rintro ⟨hp, hlo, hhi⟩
    have hlo' : Real.exp (Real.exp ((m : ℝ)-1)) ≤ p := by
      have h1 := Real.exp_le_exp.mpr hlo
      have h2 := Real.exp_le_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    have hhi' : (p : ℝ) < Real.exp (Real.exp (m : ℝ)) := by
      have h1 := Real.exp_lt_exp.mpr hhi
      have h2 := Real.exp_lt_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hp, hlo', hhi'⟩
    exact_mod_cast hhi'.le.trans (Nat.le_ceil _)

lemma mem_primeBoxTuples_iff {N : ℕ} {p m : Fin N → ℕ} :
    p ∈ primeBoxTuples m ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ unitGridCell m := by
  simp only [primeBoxTuples, Fintype.mem_piFinset, mem_unitPrimeBox_iff,
    unitGridCell, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
    primePrefixCoord]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hp, hu⟩ i
    exact ⟨hp i, hu i⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeIntervalMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint bookkeeping for reciprocal primes in half-open intervals. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma mem_primesUpTo {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p ∈ primesUpTo x ↔ p.Prime ∧ (p : ℝ)≤x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hp⟩,hprime⟩
    exact ⟨hprime,(Nat.le_floor_iff hx).mp hp⟩
  · rintro ⟨hprime,hp⟩
    exact ⟨⟨hprime.two_le,(Nat.le_floor_iff hx).mpr hp⟩,hprime⟩

private lemma mem_primesBelow {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p ∈ primesBelow x ↔ p.Prime ∧ (p : ℝ)<x := by
  simp only [primesBelow,Finset.mem_filter,mem_primesUpTo hx]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.le⟩,h.2⟩⟩

lemma primeReciprocal_endpoint_error {x : ℝ} (hx : 0<x) :
    |primeReciprocalLT x-primeReciprocalLE x| ≤ 1/x := by
  classical
  have hsub : primesBelow x⊆primesUpTo x := Finset.filter_subset _ _
  let K := primesUpTo x\primesBelow x
  have hK (p : ℕ) (hp : p∈K) : (p : ℝ)=x := by
    obtain ⟨hpU,hpL⟩ := Finset.mem_sdiff.mp hp
    have hp1 := (mem_primesUpTo hx.le).mp hpU
    have hp2 : ¬(p : ℝ)<x := by
      intro hh
      exact hpL ((mem_primesBelow hx.le).mpr ⟨hp1.1,hh⟩)
    exact le_antisymm hp1.2 (le_of_not_gt hp2)
  have hsum : (∑ p ∈ K, (p : ℝ)⁻¹)≤1/x := by
    by_cases hne : K.Nonempty
    · obtain ⟨p,hp⟩ := hne
      have heq : K={p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hp,?_⟩
        intro q hq
        exact_mod_cast (hK q hq).trans (hK p hp).symm
      simp only [heq,Finset.sum_singleton,hK p hp,one_div]
      rfl
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
      positivity
  have heq : primeReciprocalLE x-primeReciprocalLT x=∑ p ∈ K, (p : ℝ)⁻¹ := by
    exact (Finset.sum_sdiff_eq_sub hsub).symm
  have hnon : 0≤∑ p ∈ K, (p : ℝ)⁻¹ := Finset.sum_nonneg (by intros; positivity)
  rw [abs_sub_comm,heq,abs_of_nonneg hnon]
  exact hsum

lemma unitPrimeBox_reciprocal (m : ℕ) :
    (∑ p ∈ unitPrimeBox m, (p : ℝ)⁻¹)=
      primeReciprocalLT (Real.exp (Real.exp (m : ℝ)))-
      primeReciprocalLT (Real.exp (Real.exp ((m : ℝ)-1))) := by
  classical
  let a := Real.exp (Real.exp ((m : ℝ)-1))
  let b := Real.exp (Real.exp (m : ℝ))
  have ha : 0<a := Real.exp_pos _
  have hb : 0<b := Real.exp_pos _
  have hab : a≤b := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hsub : primesBelow a⊆primesBelow b := by
    intro p hp
    have hh := (mem_primesBelow ha.le).mp hp
    exact (mem_primesBelow hb.le).mpr ⟨hh.1,hh.2.trans_le hab⟩
  have hset : unitPrimeBox m=primesBelow b\primesBelow a := by
    ext p
    simp only [unitPrimeBox,Finset.mem_filter,Finset.mem_Icc,Finset.mem_sdiff,
      mem_primesBelow ha.le,mem_primesBelow hb.le]
    constructor
    · rintro ⟨⟨_,_⟩,hp,hal,hbl⟩
      exact ⟨⟨hp,hbl⟩,fun hh => (not_lt_of_ge hal) hh.2⟩
    · rintro ⟨⟨hp,hpb⟩,hpa⟩
      have hpa' : a≤(p : ℝ) := le_of_not_gt (fun hh => hpa ⟨hp,hh⟩)
      refine ⟨⟨hp.two_le,?_⟩,hp,hpa',hpb⟩
      apply (Nat.cast_le (α := ℝ)).mp
      exact hpb.le.trans (Nat.le_ceil b)
  rw [hset,Finset.sum_sdiff_eq_sub hsub]
  rfl

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

lemma primeReciprocalLT_mertens : ∃ D : ℝ, 0<D ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLT x-Real.log (Real.log x)-Mertens.M| ≤ D/Real.log x := by
  obtain ⟨C,hC,hbound⟩ := primeReciprocalLE_mertens
  refine ⟨C+1,by linarith,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  have hl : 0<Real.log x := Real.log_pos (by linarith)
  have hxlog : Real.log x≤x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have he := (primeReciprocal_endpoint_error hx0).trans
    (one_div_le_one_div_of_le hl hxlog)
  calc
    _ = |(primeReciprocalLT x-primeReciprocalLE x)+
        (primeReciprocalLE x-Real.log (Real.log x)-Mertens.M)| := by congr 1; ring
    _ ≤ |primeReciprocalLT x-primeReciprocalLE x|+
        |primeReciprocalLE x-Real.log (Real.log x)-Mertens.M| := abs_add_le _ _
    _ ≤ 1/Real.log x+C/Real.log x := add_le_add he (hbound x hx)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeShiftWeight
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A telescoping bound for replacing 1/p by 1/(p-1). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma shifted_reciprocal_error (S : Finset ℕ) {a : ℝ} (ha : 2≤a)
    (hS : ∀ p ∈ S, a≤(p : ℝ)) :
    |(∑ p ∈ S, (p-1 : ℝ)⁻¹)-(∑ p ∈ S, (p : ℝ)⁻¹)| ≤ 2/a := by
  classical
  by_cases hne : S.Nonempty
  · let L := ⌈a⌉₊
    let M := S.sup id
    have hLa : a≤(L : ℝ) := Nat.le_ceil a
    have hL : 2≤L := by exact_mod_cast (ha.trans hLa)
    have hsub : S⊆Finset.Icc L M := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(Nat.ceil_le).mpr (hS p hp),Finset.le_sup (f := id) hp⟩
    have hLM : L≤M := by
      obtain ⟨p,hp⟩ := hne
      exact (Finset.mem_Icc.mp (hsub hp)).1.trans (Finset.mem_Icc.mp (hsub hp)).2
    have hn (n : ℕ) (hn : n∈Finset.Icc L M) : (1 : ℝ)<n := by
      exact_mod_cast (show 1<n by have := (Finset.mem_Icc.mp hn).1; omega)
    have ht : (∑ n ∈ Finset.Icc L M, (((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹))=
        ((L : ℝ)-1)⁻¹-(M : ℝ)⁻¹ := by
      have hh := Finset.sum_Icc_sub hLM (fun n : ℕ => ((n : ℝ)-1)⁻¹)
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
      simpa only [← Finset.sum_neg_distrib,neg_sub] using congrArg Neg.neg hh
    have hnon (n : ℕ) (hn' : n∈Finset.Icc L M) :
        0≤((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹ := by
      apply sub_nonneg.mpr
      exact inv_anti₀ (by linarith [hn n hn']) (by linarith)
    have hnonS : 0≤∑ p ∈ S, (((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹) :=
      Finset.sum_nonneg (fun p hp => hnon p (hsub hp))
    rw [← Finset.sum_sub_distrib,abs_of_nonneg hnonS]
    calc
      _ ≤ ∑ n ∈ Finset.Icc L M, (((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnon n hn)
      _ = ((L : ℝ)-1)⁻¹-(M : ℝ)⁻¹ := ht
      _ ≤ ((L : ℝ)-1)⁻¹ := sub_le_self _ (by positivity)
      _ ≤ 2/a := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (by linarith : (0 : ℝ)<L-1) (by linarith : 0<a)).mpr
        nlinarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty,sub_self,abs_zero]
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBoxInput
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of Ford's unit-box prime sum from the proved second Mertens theorem. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem fordUnitPrimeBoxInput : FordUnitPrimeBoxInput := by
  obtain ⟨D,hD,hbound⟩ := primeReciprocalLT_mertens
  refine ⟨D*(1+Real.exp 1)+2*Real.exp 1,by positivity,?_⟩
  intro m hm
  let a := Real.exp (Real.exp ((m : ℝ)-1))
  let b := Real.exp (Real.exp (m : ℝ))
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 2≤a := by
    have hh : Real.exp 1≤a := Real.exp_le_exp.mpr (Real.one_le_exp (by linarith))
    linarith [Real.exp_one_gt_d9]
  have hab : a≤b := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hb : 2≤b := ha.trans hab
  have ha0 : 0<a := by linarith
  have hla : Real.log a=Real.exp ((m : ℝ)-1) := Real.log_exp _
  have hlb : Real.log b=Real.exp (m : ℝ) := Real.log_exp _
  have hlla : Real.log (Real.log a)=(m : ℝ)-1 := by rw [hla,Real.log_exp]
  have hllb : Real.log (Real.log b)=(m : ℝ) := by rw [hlb,Real.log_exp]
  have hmass : |primeReciprocalLT b-primeReciprocalLT a-1| ≤
      D/Real.log b+D/Real.log a := by
    calc
      _ = |(primeReciprocalLT b-Real.log (Real.log b)-Mertens.M)-
          (primeReciprocalLT a-Real.log (Real.log a)-Mertens.M)| := by
        rw [hlla,hllb]
        congr 1
        ring
      _ ≤ |primeReciprocalLT b-Real.log (Real.log b)-Mertens.M|+
          |primeReciprocalLT a-Real.log (Real.log a)-Mertens.M| := abs_sub _ _
      _ ≤ _ := add_le_add (hbound b hb) (hbound a ha)
  have he : |unitPrimeWeight m-(primeReciprocalLT b-primeReciprocalLT a)|≤2/a := by
    rw [← unitPrimeBox_reciprocal]
    exact shifted_reciprocal_error (unitPrimeBox m) ha
      (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
  have hsmall : 2/a≤2/Real.log a := by
    apply div_le_div_of_nonneg_left (by norm_num) (Real.log_pos (by linarith))
    linarith [Real.log_le_sub_one_of_pos ha0]
  have htotal : |unitPrimeWeight m-1|≤D/Real.log b+(D+2)/Real.log a := by
    calc
      _ ≤ |unitPrimeWeight m-(primeReciprocalLT b-primeReciprocalLT a)|+
          |(primeReciprocalLT b-primeReciprocalLT a)-1| := abs_sub_le _ _ _
      _ ≤ 2/a+(D/Real.log b+D/Real.log a) := add_le_add he hmass
      _ ≤ 2/Real.log a+(D/Real.log b+D/Real.log a) := add_le_add hsmall le_rfl
      _ = _ := by ring
  have heq : D/Real.log b+(D+2)/Real.log a=
      (D*(1+Real.exp 1)+2*Real.exp 1)*Real.exp (-(m : ℝ)) := by
    rw [hla,hlb]
    simp only [div_eq_mul_inv,← Real.exp_neg]
    rw [show -((m : ℝ)-1)=1+ -(m : ℝ) by ring,Real.exp_add]
    ring
  exact heq ▸ htotal

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixLower
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagating the first discrete tail coordinate through the prefix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The renewal recurrence propagates any terminal lower bound through the
triangular prefix inequalities. This includes the first discrete tail prime. -/
theorem renewal_prefix_lower (N : ℕ) (u : ℕ → ℝ)
    (hs : ∀ i < N, (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*u j) ≤ u i)
    {i : ℕ} (hi : i ≤ N) : g (N-i)*u N ≤ u i := by
  have hmain : ∀ d : ℕ, ∀ j : ℕ, j+d=N → g d*u N ≤ u j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj
      by_cases hd : d = 0
      · subst d
        have hjN : j = N := by omega
        simp [hjN, g]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have hrec := g_convolution hdpos
        calc
          g d*u N = ∑ r ∈ Finset.range d, a (d-r)*(g r*u N) := by
            rw [hrec, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ ≤ ∑ r ∈ Finset.range d, a (d-r)*u (N-r) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrd := Finset.mem_range.mp hr
            apply mul_le_mul_of_nonneg_left
              (ih r hrd (N-r) (by omega)) (a_pos (by omega)).le
          _ = ∑ k ∈ Finset.Icc (j+1) N, a (k-j)*u k := by
            apply Finset.sum_bij (fun r _ => N-r)
            · intro r hr
              have := Finset.mem_range.mp hr
              exact Finset.mem_Icc.mpr (by omega)
            · intro r hr s hs hrs
              have := Finset.mem_range.mp hr
              have := Finset.mem_range.mp hs
              omega
            · intro k hk
              have := Finset.mem_Icc.mp hk
              exact ⟨N-k, Finset.mem_range.mpr (by omega), by omega⟩
            · intro r hr
              have := Finset.mem_range.mp hr
              congr 2
              omega
          _ ≤ u j := hs j (by omega)
  exact hmain (N-i) i (Nat.add_sub_of_le hi)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalLower
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform lower bounds for renewal coefficients and unbanded prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_pos (n : ℕ) : 0 < normalizedRenewal n :=
  mul_pos (g_pos _) (pow_pos rho_pos _)

lemma renewal_uniform_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*(rho^n)⁻¹ ≤ g n := by
  have hlim := (normalizedRenewal_properties hford).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show gamma/2 < gamma by linarith [gamma_pos])))
  let T := insert (gamma/2) ((Finset.range N).image normalizedRenewal)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let c := T.min' hT
  have hc : 0 < c := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact div_pos gamma_pos (by norm_num)
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
      exact normalizedRenewal_pos n
  refine ⟨c, hc, fun n => ?_⟩
  have hh : c ≤ normalizedRenewal n := by
    by_cases hn : n < N
    · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hN n (by omega)).le
  have hp := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  simpa only [normalizedRenewal, mul_assoc, mul_inv_cancel₀ (pow_pos rho_pos n).ne', mul_one]
    using hp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConcavity
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete concavity of the coefficients in Ford's renewal recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_shift_integral (j k : ℕ) :
    a (j+k)=∫ t in (j : ℝ)..(j+1 : ℝ), Real.log (t+k) := by
  rw [a_eq_integral,intervalIntegral.integral_comp_add_right]
  push_cast
  congr 1
  ring

lemma log_shift_intervalIntegrable {j : ℕ} (hj : 1≤j) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t+k)) MeasureTheory.volume j (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
  intro t ht
  have hn : t+(k : ℝ)≠0 := by
    have hk : (0 : ℝ)≤k := Nat.cast_nonneg _
    linarith [ht.1]
  exact ((continuousAt_id.add continuousAt_const).log hn).continuousWithinAt

lemma log_second_difference_pos {t : ℝ} (ht : 0<t) :
    0<2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
  have ht2 : 0<t+2 := by linarith
  have hh := Real.log_lt_log (mul_pos ht ht2)
    (show t*(t+2)<(t+1)^2 by nlinarith)
  rw [Real.log_mul ht.ne' ht2.ne',Real.log_pow] at hh
  norm_num at hh
  linarith

/-- The strict second difference used in Ford Lemma 3.7. -/
lemma a_second_difference_neg {j : ℕ} (hj : 1≤j) :
    a (j+2)-2*a (j+1)+a j<0 := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hc : ContinuousOn
      (fun t : ℝ => 2*Real.log (t+1)-(Real.log t+Real.log (t+2)))
      (Set.Icc (j : ℝ) (j+1)) := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht1 : t+1≠0 := by linarith [ht.1]
    have ht2 : t+2≠0 := by linarith [ht.1]
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht1)).sub
      ((continuousAt_id.log ht0).add ((continuousAt_id.add continuousAt_const).log ht2))).continuousWithinAt
  have hi : 0<∫ t in (j : ℝ)..(j+1 : ℝ),
      2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
    apply intervalIntegral.integral_pos (by linarith) hc
    · intro t ht
      exact (log_second_difference_pos (by linarith [ht.1])).le
    · refine ⟨j+1,⟨by linarith,le_rfl⟩,?_⟩
      exact log_second_difference_pos (by linarith)
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have h2 := log_shift_intervalIntegrable hj 2
  have he1 := a_shift_integral j 1
  have he2 := a_shift_integral j 2
  simp only [Nat.cast_one,Nat.cast_ofNat] at h1 h2 he1 he2
  simp only [Nat.cast_zero,add_zero] at h0
  rw [intervalIntegral.integral_sub (h1.const_mul 2) (h0.add h2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_add h0 h2,
    ← he1,← he2,← a_eq_integral j] at hi
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeparation
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small root separation for the sign of Ford's transformed coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalSeries_three_sevenths_lt_one : renewalSeries (3/7)<1 := by
  let r : ℝ := 3/7
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r<1 := by norm_num [r]
  have hs := summable_renewal hr0 hr1
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := r) (by norm_num [r])
  have hsg : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1)) (21/16 : ℝ) := by
    have h2 := hg.mul_right r
    have e1 : (fun i : ℕ => (((i + 1).choose 1 : ℕ) : ℝ) * r ^ i * r) =
        fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1) := by
      ext n
      simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    have e2 : (1 / (1 - r) ^ (1 + 1)) * r = (21/16 : ℝ) := by norm_num [r]
    rw [e1, e2] at h2
    exact h2
  have htail : (∑' n : ℕ, a (n+2+1)*r^(n+2+1)) ≤
      ∑' n : ℕ, ((n+2+1 : ℕ) : ℝ)*r^(n+2+1) := by
    apply ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum
    · intro n
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast a_le_index (j := n+2+1) (by omega)) (pow_nonneg hr0 _)
    · exact (summable_nat_add_iff 2).mpr hsg.summable
  have hf := hs.sum_add_tsum_nat_add 2
  have hi := hsg.summable.sum_add_tsum_nat_add 2
  rw [hsg.tsum_eq] at hi
  change _=renewalSeries r at hf
  norm_num [Finset.sum_range_succ,r] at hf hi htail
  have ha1 : a 1<1/2 := by
    norm_num [a]
    linarith [Real.log_two_lt_d9]
  have ha2 : a 2<1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  change renewalSeries r<1
  nlinarith

lemma rho_gt_three_sevenths : (3/7 : ℝ) < rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho∈Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩)
    (show (3/7 : ℝ)∈Set.Ico (0 : ℝ) 1 by norm_num) hh
  rw [renewalSeries_rho] at hm
  linarith [renewalSeries_three_sevenths_lt_one]

lemma renewal_first_transformed_negative : rho⁻¹-a 1-2<0 := by
  have hr : rho⁻¹<(7/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_sevenths]
  have ha : (1/3 : ℝ)<a 1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9]
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalTail
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail coefficients in (1-F(z))/(1-z/rho). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_le_a_succ {j : ℕ} (hj : 1≤j) : a j≤a (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have he1 := a_shift_integral j 1
  simp only [Nat.cast_zero,add_zero] at h0
  simp only [Nat.cast_one] at h1 he1
  rw [a_eq_integral,he1]
  apply intervalIntegral.integral_mono_on (by linarith) h0 h1
  intro t ht
  apply Real.log_le_log (by linarith [ht.1])
  linarith

lemma summable_renewalTail (n : ℕ) :
    Summable (fun k : ℕ => a (n+k+1)*rho^(k+1)) := by
  have hgeo : Summable (fun k : ℕ => rho^(k+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one rho_pos.le rho_lt_one)
  have hmajor := (hgeo.mul_left (n : ℝ)).add
    (summable_index_geometric rho_pos.le rho_lt_one 1)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le) _ hmajor
  intro k
  have hh := mul_le_mul_of_nonneg_right (a_le_index (j := n+k+1) (by omega))
    (pow_pos rho_pos (k+1)).le
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma renewalTail_zero : renewalTail 0=1 := by
  simpa only [renewalTail,Nat.zero_add,renewalSeries] using renewalSeries_rho

lemma renewalTail_nonneg (n : ℕ) : 0 ≤ renewalTail n :=
  tsum_nonneg (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le)

lemma renewalTail_le_succ (n : ℕ) : renewalTail n ≤ renewalTail (n+1) := by
  apply (summable_renewalTail n).tsum_le_tsum _ (summable_renewalTail (n+1))
  intro k
  apply mul_le_mul_of_nonneg_right _ (pow_pos rho_pos _).le
  convert a_le_a_succ (j := n+k+1) (by omega) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

lemma renewalTail_recurrence (n : ℕ) :
    renewalTail n=rho*a (n+1)+rho*renewalTail (n+1) := by
  have hs := (summable_renewalTail n).sum_add_tsum_nat_add 1
  have he : (∑' k : ℕ, a (n+(k+1)+1)*rho^(k+1+1))=rho*renewalTail (n+1) := by
    rw [renewalTail,← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    have hn : n+(k+1)+1=(n+1)+k+1 := by omega
    rw [hn]
    ring
  change _=renewalTail n at hs
  simp only [Finset.sum_range_one,Nat.add_zero,Nat.zero_add,pow_one] at hs
  rw [he] at hs
  simpa only [mul_comm] using hs.symm

lemma renewalTail_second_difference_neg (n : ℕ) :
    renewalTail (n+2)-2*renewalTail (n+1)+renewalTail n<0 := by
  have hs0 := summable_renewalTail n
  have hs1 := summable_renewalTail (n+1)
  have hs2 := summable_renewalTail (n+2)
  have he : renewalTail (n+2)+renewalTail n<2*renewalTail (n+1) := by
    rw [renewalTail,renewalTail,renewalTail,← hs2.tsum_add hs0,← tsum_mul_left]
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      have hd := a_second_difference_neg (j := n+k+1) (by omega)
      have hpow := pow_pos rho_pos (k+1)
      have he1 : n+k+1+1=n+1+k+1 := by omega
      have he2 : n+k+1+2=n+2+k+1 := by omega
      rw [he1,he2] at hd
      nlinarith
    · have hd := a_second_difference_neg (j := n+1) (by omega)
      simp only [Nat.add_zero,Nat.zero_add,pow_one]
      have he1 : n+1+1=n+2 := by omega
      rw [he1] at hd
      have hp := mul_lt_mul_of_pos_right hd rho_pos
      nlinarith [hp]
    · exact hs2.add hs0
    · exact hs1.mul_left 2
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMoment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the tail generating series at its renewal root. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma momentPair_nonneg (p : ℕ×ℕ) : 0 ≤ momentPair p :=
  mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le

private lemma momentPair_diagonal (n : ℕ) :
    (∑ p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p)=
      (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
  rw [Finset.sum_coe_sort]
  have he : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, momentPair p)=
      ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, a (n+1)*rho^(n+1) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [momentPair,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

private lemma summable_momentPair : Summable momentPair := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hs : Summable (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2) := by
    apply (summable_sigma_of_nonneg
      (f := fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2)
      (fun p => momentPair_nonneg p.2)).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,momentPair_diagonal] using summable_moment
  exact e.summable_iff.mp hs

lemma renewalTail_weighted_sum :
    Summable (fun n : ℕ => renewalTail n*rho^n) ∧
      (∑' n : ℕ, renewalTail n*rho^n)=gamma⁻¹ := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have he (n : ℕ) : renewalTail n*rho^n=∑' k : ℕ, momentPair (n,k) := by
    rw [renewalTail,← tsum_mul_right]
    apply tsum_congr
    intro k
    dsimp [momentPair]
    rw [mul_assoc,← pow_add]
    congr 2
    omega
  have hsum := (summable_prod_of_nonneg momentPair_nonneg).mp summable_momentPair
  refine ⟨?_,?_⟩
  · simpa only [he] using hsum.2
  · calc
      _ = ∑' n : ℕ, ∑' k : ℕ, momentPair (n,k) := tsum_congr he
      _ = ∑' p : ℕ×ℕ, momentPair p := summable_momentPair.tsum_prod.symm
      _ = ∑' p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p.2 :=
        (e.tsum_eq momentPair).symm
      _ = ∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p :=
        (e.summable_iff.mpr summable_momentPair).tsum_sigma
      _ = ∑' n : ℕ, (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
        apply tsum_congr
        intro n
        rw [tsum_fintype,momentPair_diagonal]
      _ = gamma⁻¹ := by simp [gamma]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalKernel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative transformed kernel in Ford's renewal argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalIncrement_nonneg (n : ℕ) : 0 ≤ renewalIncrement n :=
  sub_nonneg.mpr (renewalTail_le_succ n)

lemma renewalKernel_pos (n : ℕ) : 0 < renewalKernel n := by
  cases n with
  | zero =>
    have hh := renewalTail_recurrence 0
    rw [renewalTail_zero] at hh
    have he : renewalTail 1=rho⁻¹-a 1 := by
      apply (mul_left_cancel₀ rho_pos.ne')
      calc
        rho*renewalTail 1=1-rho*a 1 := by linarith
        _ = rho*(rho⁻¹-a 1) := by field_simp [rho_pos.ne']
    simpa only [renewalKernel,renewalIncrement,renewalTail_zero,he] using
      (show 0<1-((rho⁻¹-a 1)-1) by linarith [renewal_first_transformed_negative])
  | succ n =>
    have hh := renewalTail_second_difference_neg n
    change 0<(renewalTail (n+1)-renewalTail n)-
      (renewalTail (n+1+1)-renewalTail (n+1))
    have he : n+1+1=n+2 := by omega
    rw [he]
    linarith

lemma renewalKernel_partial_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalKernel j)=1-renewalIncrement n := by
  induction n with
  | zero => simp [renewalKernel]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,renewalKernel]
    ring

lemma renewalKernel_sum_le_one (n : ℕ) :
    (∑ j ∈ Finset.range n, renewalKernel j)≤1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [renewalKernel_partial_sum]
    linarith [renewalIncrement_nonneg n]

lemma renewalResolvent_bounds (n : ℕ) : 0 ≤ renewalResolvent n ∧ renewalResolvent n≤1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [renewalResolvent]
    | succ n =>
      have hindex (j : ℕ) (hj : j∈Finset.range (n+1)) : n-j<n+1 := by omega
      constructor
      · rw [renewalResolvent]
        exact Finset.sum_nonneg (fun j hj => mul_nonneg (renewalKernel_pos j).le
          (ih (n-j) (hindex j hj)).1)
      · rw [renewalResolvent]
        calc
          _ ≤ ∑ j ∈ Finset.range (n+1), renewalKernel j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_of_le_one_right (renewalKernel_pos j).le (ih (n-j) (hindex j hj)).2
          _ ≤ 1 := renewalKernel_sum_le_one (n+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeriesAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal coefficient identities for Ford's transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma U_kernel_identity : Useries*(1-PowerSeries.X*Pseries)=1 := by
  have he : Useries*(1-PowerSeries.X*Pseries)=Useries-PowerSeries.X*(Pseries*Useries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Useries,renewalResolvent]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,Pseries,renewalResolvent,sub_self]

private lemma kernel_factorization : (1-PowerSeries.X)^2*Lseries=1-PowerSeries.X*Pseries := by
  have he : (1-PowerSeries.X)^2*Lseries=
      Lseries-PowerSeries.X*Lseries-PowerSeries.X*Lseries+
        PowerSeries.X*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,renewalTail_zero]
  | succ n =>
    cases n with
    | zero =>
      simp [PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,Lseries,Pseries,
        renewalKernel,renewalIncrement,renewalTail_zero]
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Lseries,Pseries,
        PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false,
        renewalKernel,renewalIncrement]
      ring

private lemma L_H_identity : Lseries*Hseries=1 := by
  calc
    _ = Useries*((1-PowerSeries.X)^2*Lseries) := by dsimp [Hseries] <;> ring
    _ = Useries*(1-PowerSeries.X*Pseries) := by rw [kernel_factorization]
    _ = 1 := U_kernel_identity

private lemma L_A_identity : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=1-Aseries := by
  have he : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=
      Lseries-PowerSeries.C rho⁻¹*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,Aseries,renewalTail_zero]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,Lseries,Aseries,
      PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    have he := renewalTail_recurrence n
    have hh : rho⁻¹*renewalTail n=a (n+1)+renewalTail (n+1) := by
      rw [he]
      field_simp [rho_pos.ne']
    linarith

private lemma G_A_identity : Gseries*(1-Aseries)=1 := by
  have he : Gseries*(1-Aseries)=Gseries-PowerSeries.X*(PowerSeries.mk (fun n => a (n+1))*Gseries) := by
    dsimp [Aseries]
    ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Gseries,g]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Gseries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,g,sub_self]

private lemma G_H_identity : Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)=Hseries := by
  calc
    _ = Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)*(Lseries*Hseries) := by rw [L_H_identity,mul_one]
    _ = (Gseries*((1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries))*Hseries := by ring
    _ = (Gseries*(1-Aseries))*Hseries := by rw [L_A_identity]
    _ = Hseries := by rw [G_A_identity,one_mul]

lemma renewalRegular_bound (n : ℕ) : |renewalRegular n|≤4 := by
  have he : Hseries=Useries-PowerSeries.X*Useries-PowerSeries.X*Useries+
        PowerSeries.X*(PowerSeries.X*Useries) := by dsimp [Hseries] <;> ring
  rw [renewalRegular,he]
  cases n with
  | zero => norm_num [PowerSeries.coeff_zero_X_mul,Useries,renewalResolvent]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,
        Useries,PowerSeries.coeff_mk]
      norm_num only [show renewalResolvent 0=1 by rw [renewalResolvent],zero_add,add_zero]
      have hb := renewalResolvent_bounds 1
      rw [abs_le]
      constructor <;> linarith
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk]
      have h0 := renewalResolvent_bounds n
      have h1 := renewalResolvent_bounds (n+1)
      have h2 := renewalResolvent_bounds (n+1+1)
      rw [abs_le]
      constructor <;> linarith

lemma renewalRegular_zero : renewalRegular 0=1 := by
  simp [renewalRegular,Hseries,Useries,renewalResolvent]

lemma renewalRegular_recurrence (n : ℕ) :
    renewalRegular (n+1)=g (n+1)-rho⁻¹*g n := by
  have h := congrArg (PowerSeries.coeff (n+1)) G_H_identity
  rw [mul_sub,mul_one] at h
  have he : Gseries*(PowerSeries.C rho⁻¹*PowerSeries.X)=
      PowerSeries.C rho⁻¹*(Gseries*PowerSeries.X) := by ring
  rw [he] at h
  simpa only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_mul_X,Gseries,
    PowerSeries.coeff_mk,renewalRegular] using h.symm

lemma renewalTail_regular_convolution (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))=
      if n=0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) L_H_identity
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Lseries,PowerSeries.coeff_mk,renewalRegular,PowerSeries.coeff_one] using h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalRegularSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant term at the renewal pole, using absolutely convergent sums. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma summable_norm_regular_weighted :
    Summable (fun n : ℕ => ‖renewalRegular n*rho^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left 4)
  intro n
  rw [norm_mul,Real.norm_eq_abs (rho^n),abs_of_pos (pow_pos rho_pos n),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (renewalRegular_bound n) (pow_pos rho_pos n).le

lemma regular_weighted_sum_eq_gamma :
    (∑' n : ℕ, renewalRegular n*rho^n)=gamma := by
  have hL : Summable (fun n : ℕ => ‖renewalTail n*rho^n‖) := by
    convert renewalTail_weighted_sum.1 using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact Real.norm_of_nonneg (mul_nonneg (renewalTail_nonneg n) (pow_pos rho_pos n).le)
  have ht := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hL summable_norm_regular_weighted
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1),
      (renewalTail j*rho^j)*(renewalRegular (n-j)*rho^(n-j)))=
      if n=0 then 1 else 0 := by
    calc
      _ = (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))*rho^n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
        have hp : rho^j*rho^(n-j)=rho^n := by rw [← pow_add,Nat.add_sub_of_le hjn]
        calc
          _ = (renewalTail j*renewalRegular (n-j))*(rho^j*rho^(n-j)) := by ring
          _ = _ := by rw [hp]
      _ = _ := by rw [renewalTail_regular_convolution]; split_ifs with hn <;> simp [hn]
  simp only [he] at ht
  rw [renewalTail_weighted_sum.2] at ht
  have hs : (∑' n : ℕ, if n=0 then (1 : ℝ) else 0)=1 := by simp
  rw [hs] at ht
  have hmul := congrArg (fun x : ℝ => gamma*x) ht
  simpa only [← mul_assoc,mul_inv_cancel₀ gamma_pos.ne',one_mul,mul_one] using hmul

lemma normalized_renewal_eq_regular_partial (n : ℕ) :
    g n*rho^n=∑ j ∈ Finset.range (n+1), renewalRegular j*rho^j := by
  induction n with
  | zero => simp [g,renewalRegular_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih,renewalRegular_recurrence,pow_succ]
    field_simp [rho_pos.ne']
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalInput
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of Ford Lemma 3.7 by the concrete transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma regular_tail_bound (n : ℕ) :
    |∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)|≤4*rho/(1-rho) := by
  have hg : HasSum (fun k : ℕ => 4*rho^(k+1)) (4*rho/(1-rho)) := by
    have h2 := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left (4*rho)
    have e1 : (fun k : ℕ => 4*rho * rho^k) = fun k : ℕ => 4*rho^(k+1) := by
      ext k
      rw [pow_succ]
      ring
    have e2 : 4*rho*(1-rho)⁻¹ = 4*rho/(1-rho) := by rw [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  have hb (k : ℕ) : ‖renewalRegular (k+n+1)*rho^(k+1)‖≤4*rho^(k+1) := by
    rw [norm_mul,Real.norm_eq_abs (rho^(k+1)),abs_of_pos (pow_pos rho_pos _),Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (renewalRegular_bound _) (pow_pos rho_pos _).le
  have hs : Summable (fun k : ℕ => ‖renewalRegular (k+n+1)*rho^(k+1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg.summable
  calc
    _ = ‖∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖renewalRegular (k+n+1)*rho^(k+1)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, 4*rho^(k+1) := hs.tsum_le_tsum hb hg.summable
    _ = _ := hg.tsum_eq

/-- The bounded renewal error assumed throughout the conditional development
is now proved. A coarse explicit constant suffices for every application. -/
theorem fordRenewalInput : FordRenewalInput := by
  refine ⟨4*rho/(1-rho),div_nonneg (mul_nonneg (by norm_num) rho_pos.le) (by linarith [rho_lt_one]),?_⟩
  intro n
  have hp : rho^n≠0 := (pow_pos rho_pos n).ne'
  have hs := summable_norm_regular_weighted.of_norm.sum_add_tsum_nat_add (n+1)
  rw [regular_weighted_sum_eq_gamma,← normalized_renewal_eq_regular_partial n] at hs
  have he : (∑' k : ℕ, renewalRegular (k+(n+1))*rho^(k+(n+1)))=
      (∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1))*rho^n := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro k
    have hpow : rho^(k+(n+1))=rho^(k+1)*rho^n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hn : k+(n+1)=k+n+1 := by omega
    rw [hn]
    ring
  rw [he] at hs
  have herror : g n-gamma*(rho^n)⁻¹= -∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1) := by
    apply (mul_right_cancel₀ hp)
    calc
      (g n-gamma*(rho^n)⁻¹)*rho^n=g n*rho^n-gamma := by field_simp
      _ = _ := by nlinarith [hs]
  rw [herror,abs_neg]
  exact regular_tail_bound n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedPrefixLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Terminal lower bounds for finite unbanded simplex prefixes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma enlargedSimplex_mul_const {N : ℕ} {B β₀ c : ℝ} {β u : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N B β₀ β) (hc : 0 ≤ c) :
    (fun i => c*u i) ∈ enlargedSimplex N (c*B) β₀ β := by
  refine ⟨fun i => mul_nonneg hc (hu.1 i),?_,?_⟩
  · intro i
    calc
      _ = c*∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ ≤ c*(β i*u i) := mul_le_mul_of_nonneg_left (hu.2.1 i) hc
      _ = _ := by ring
  · calc
      _ = c*∑ i : Fin N, a (i.val+1)*u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ c*(β₀*B) := mul_le_mul_of_nonneg_left hu.2.2 hc
      _ = _ := by ring

lemma prefixRegion_last_lower {N : ℕ} {B : ℝ} {u : Fin (N+1) → ℝ}
    (hu : u ∈ prefixRegion (N+1) B 0 0) (i : Fin (N+1)) :
    g (N-i.val)*u (Fin.last N) ≤ u i := by
  let v : ℕ → ℝ := fun j => if hj : j < N+1 then u ⟨j,hj⟩ else 0
  have hv (j) (hj : j < N+1) : v j = u ⟨j,hj⟩ := by simp only [v,dite_eq_left hj]
  have hs (j : ℕ) (hj : j < N) :
      (∑ r ∈ Finset.Icc (j+1) N, a (r-j)*v r) ≤ v j := by
    have hh := hu.1 ⟨j,by omega⟩
    rw [prefixLinear_apply] at hh
    have he : (∑ r : Fin (N+1), if (⟨j,by omega⟩:Fin (N+1)) < r then
        a (r.val-j)*u r else 0) =
        ∑ r ∈ Finset.Icc (j+1) N, a (r-j)*v r := by
      have hv' : (∑ r : Fin (N+1), if j < r.val then a (r.val-j)*u r else 0) =
          ∑ r : Fin (N+1), if j < r.val then a (r.val-j)*v r.val else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hv r.val r.isLt]
      change (∑ r : Fin (N+1), if j < r.val then a (r.val-j)*u r else 0) = _
      rw [hv',Fin.sum_univ_eq_sum_range
        (fun r => if j < r then a (r-j)*v r else 0), ← Finset.sum_filter]
      congr 1
      ext r
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
      omega
    rw [he] at hh
    rw [hv j (by omega)]
    change 0 ≤ u ⟨j,by omega⟩-_ at hh
    linarith
  have hh := renewal_prefix_lower N v hs (show i.val ≤ N by omega)
  simpa only [hv N (by omega),hv i.val i.isLt,Fin.eta,Fin.last] using hh

lemma renewal_linear_lower : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*((n:ℝ)+1) ≤ g n := by
  obtain ⟨d,hd,hg⟩ := renewal_uniform_lower fordRenewalInput
  let r := min 1 (rho⁻¹-1)
  have hrpos : 0 < r := lt_min (by norm_num) (by
    have hh : 1 < rho⁻¹ := (one_lt_inv₀ rho_pos).mpr rho_lt_one
    linarith)
  refine ⟨d*r,mul_pos hd hrpos,fun n => ?_⟩
  have hp := one_add_mul_sub_le_pow (show (-1:ℝ) ≤ rho⁻¹ from (by norm_num : (-1:ℝ) ≤ 0).trans (inv_pos.mpr rho_pos).le) n
  have hr1 : r ≤ 1 := min_le_left _ _
  have hr2 : r ≤ rho⁻¹-1 := min_le_right _ _
  have hn := mul_le_mul_of_nonneg_left hr2 (Nat.cast_nonneg n (α:=ℝ))
  have hh : r*((n:ℝ)+1) ≤ (rho^n)⁻¹ := by
    rw [← inv_pow]
    nlinarith only [hr1,hn,hp]
  calc
    _ = d*(r*((n:ℝ)+1)) := by ring
    _ ≤ d*(rho^n)⁻¹ := mul_le_mul_of_nonneg_left hh hd.le
    _ ≤ g n := hg n

/-- The linear lower envelope survives every bounded diagonal enlargement. -/
theorem enlarged_prefix_linear_lower : ∃ d : ℝ, 0 < d ∧
    ∀ {N : ℕ} {B β₀ K : ℝ} {β κ u : Fin (N+1) → ℝ},
      0 < K → 0 < β₀ → (∀ i, 0 < β i) →
      (∀ i, 1 ≤ κ i ∧ κ i ≤ K) →
      (∀ i, β₀ ≤ κ i) → (∀ i j, i < j → β i*κ i ≤ κ j) →
      u ∈ enlargedSimplex (N+1) B β₀ β → 1 ≤ u (Fin.last N) →
      ∀ i, d/K*((N+1-i.val:ℕ):ℝ) ≤ u i := by
  obtain ⟨d,hd,hg⟩ := renewal_linear_lower
  refine ⟨d,hd,?_⟩
  intro N B β₀ K β κ u hK hβ₀ hβ hκ htop hstep hu hlast i
  have hκpos (j) : 0 < κ j := zero_lt_one.trans_le (hκ j).1
  have hv := enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu
  have hterminal : 1/K ≤ simplexScale κ u (Fin.last N) := by
    rw [simplexScale_apply]
    calc
      _ ≤ 1/κ (Fin.last N) := div_le_div_of_nonneg_left (by norm_num)
        (hκpos _) (hκ _).2
      _ ≤ _ := div_le_div_of_nonneg_right hlast (hκpos _).le
  have hrec := prefixRegion_last_lower hv i
  have huupper : simplexScale κ u i ≤ u i := by
    rw [simplexScale_apply]
    exact div_le_self (hu.1 i) (hκ i).1
  have hN : ((N+1-i.val:ℕ):ℝ)=((N-i.val:ℕ):ℝ)+1 := by
    exact_mod_cast (show N+1-i.val=(N-i.val)+1 by have := i.isLt; omega)
  calc
    _ = (d*((N-i.val:ℕ):ℝ)+d)*(1/K) := by rw [hN]; ring
    _ ≤ g (N-i.val)*(1/K) := mul_le_mul_of_nonneg_right
      (by simpa only [mul_add,mul_one] using hg (N-i.val)) (by positivity)
    _ ≤ g (N-i.val)*simplexScale κ u (Fin.last N) :=
      mul_le_mul_of_nonneg_left hterminal (g_pos _).le
    _ ≤ simplexScale κ u i := hrec
    _ ≤ u i := huupper

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedEnlargementLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform linear envelope for Ford's reverse-indexed enlarged prefixes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem reverse_enlarged_linear_lower : ∃ c : ℝ, 0 < c ∧
    ∀ m N : ℕ, N ≤ m → ∀ B : ℝ, ∀ u : Fin N → ℝ,
      u ∈ enlargedSimplex N B (1+simplexBoxError 0 m)
        (fun i => 1+simplexBoxError 0 (m-(i.val+1))) →
      (∀ i, i.val+1=N → (1/100:ℝ) ≤ u i) → ∀ i, c*(N-i.val:ℕ) ≤ u i := by
  obtain ⟨d,hd,hlower⟩ := enlarged_prefix_linear_lower
  let E := Real.exp (∑' n : ℕ, (n:ℝ)*simplexBoxError 0 n)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨d/(100*E),div_pos hd (mul_pos (by norm_num) hE),?_⟩
  intro m N hNm B u hu hlast
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ N =>
    let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m-r)
    let κ : Fin (N+1) → ℝ := enlargementScale β
    have hβ (r) : 1 ≤ β r := by
      dsimp [β]
      linarith [simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m-r)]
    have hκ (i) : 1 ≤ κ i ∧ κ i ≤ E := by
      refine ⟨(hβ 0).trans (enlargementScale_top hβ i),?_⟩
      have hh := reverse_enlargement_coordinate (m:=m) (H:=0) (Nat.zero_le m)
        (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
        (summable_simplexBoxError_weighted 0) i (by have := i.isLt; omega)
      simpa only [Nat.zero_add] using hh
    have hh := hlower hE (zero_lt_one.trans_le (hβ 0))
      (fun i => zero_lt_one.trans_le (hβ (i.val+1))) hκ
      (enlargementScale_top hβ) (enlargementScale_step hβ)
      (enlargedSimplex_mul_const hu (by norm_num : (0:ℝ) ≤ 100))
      (by have ht := hlast (Fin.last N) (by simp); linarith)
    intro i
    have hi := hh i
    calc
      _ = (d/E*((N+1-i.val:ℕ):ℝ))/100 := by ring
      _ ≤ u i := (div_le_iff₀ (by norm_num : (0:ℝ)<100)).mpr (by linarith only [hi])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes around a simplex prefix, without coordinate-band hypotheses. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixCubeCost_nonneg (N : ℕ) : 0 ≤ prefixCubeCost N := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (g_pos _).le (sq_nonneg _)))

lemma prefixRegion_unit_cube {N : ℕ} {B : ℝ} {u v : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (hd : ∀ i, |u i-v i| ≤ 1) :
    v ∈ prefixRegion N (B+(N:ℝ)^2) 0
      (fun i => -((N-i.val:ℕ):ℝ)^2) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hh := (le_abs_self _).trans (prefixLinear_cube_error u v hd i)
    have hi := hu.1 i
    change 0 ≤ prefixLinear N u i at hi
    linarith
  · have hh := (neg_le_abs _).trans (prefixBudget_cube_error u v hd)
    have hi := hu.2
    simp only [sub_zero] at hi ⊢
    linarith

lemma simplexScale_unit_distance {N : ℕ} {κ u v : Fin N → ℝ}
    (hκ : ∀ i, 1 ≤ κ i) (hd : ∀ i, |u i-v i| ≤ 1) :
    ∀ i, |simplexScale κ u i-simplexScale κ v i| ≤ 1 := by
  intro i
  simp only [simplexScale_apply, ← sub_div, abs_div, abs_of_pos (zero_lt_one.trans_le (hκ i))]
  exact (div_le_iff₀ (zero_lt_one.trans_le (hκ i))).mpr (by
    simpa only [one_mul] using (hd i).trans (hκ i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedCubeCost
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive unit-box cost is uniformly comparable to one renewal coefficient. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma summable_shifted_square_geometric :
    Summable (fun n : ℕ => ((n:ℝ)+1)^2*rho^n) := by
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one rho_pos.le rho_lt_one
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [pow_one]
  ring

theorem prefixCubeCost_normalized_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, prefixCubeCost N*rho^N ≤ C := by
  obtain ⟨K,hK,hg⟩ := (normalizedRenewal_properties fordRenewalInput).2
  let S := ∑' n : ℕ, ((n:ℝ)+1)^2*rho^n
  have hS : 0 < S := by
    have hh := summable_shifted_square_geometric.le_tsum 0
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
    norm_num at hh
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hh
  refine ⟨(1+K)*S, mul_pos (by linarith) hS, fun N => ?_⟩
  have hfirst : (N:ℝ)^2*rho^N ≤ S := by
    apply le_trans _ (summable_shifted_square_geometric.le_tsum N
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _)))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_pos.le _)
    nlinarith [Nat.cast_nonneg N (α:=ℝ)]
  have hsum : (∑ i : Fin N, g (i.val+1)*((N-i.val:ℕ):ℝ)^2)*rho^N ≤ K*S := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin N, K*(((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : i.val+1+(N-i.val-1)=N := by omega
        have he : ((N-i.val:ℕ):ℝ)=((N-i.val-1:ℕ):ℝ)+1 := by
          exact_mod_cast (show N-i.val=N-i.val-1+1 by omega)
        have hh : g (i.val+1)*rho^(i.val+1) ≤ K := by
          have hh := hg (i.val+1)
          rw [Real.norm_eq_abs, abs_of_pos (normalizedRenewal_pos _)] at hh
          exact hh
        have hm := mul_le_mul_of_nonneg_right hh
          (show 0 ≤ (((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) by exact mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
        have hp : rho^N = rho^(i.val+1)*rho^(N-i.val-1) := by
          rw [← pow_add, hi]
        rw [hp, he]
        nlinarith only [hm]
      _ = K*∑ j ∈ Finset.range N, ((j:ℝ)+1)^2*rho^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_bij (fun i _ => N-i.val-1)
        · intro i _
          exact Finset.mem_range.mpr (by omega)
        · intro i _ j _ hij
          apply Fin.ext
          have := i.isLt
          have := j.isLt
          omega
        · intro j hj
          have hj := Finset.mem_range.mp hj
          exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
        · intro i _
          ring
      _ ≤ K*S := mul_le_mul_of_nonneg_left
        (summable_shifted_square_geometric.sum_le_tsum _
          (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))) hK
  unfold prefixCubeCost
  rw [add_mul]
  nlinarith only [hfirst,hsum]

/-- For prefixes ending `H` coordinates before the natural dimension, the
unit-box enlargement has a uniformly bounded relative volume cost. -/
theorem prefixCubeCost_relative_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ N ≤ m x,
      (N:ℝ)*prefixCubeCost N/B x ≤ C*rho^(m x-N) := by
  obtain ⟨A,hA,ha⟩ := prefixCubeCost_normalized_bound
  refine ⟨2*A/lam, div_pos (mul_pos (by norm_num) hA) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound, B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hN
  have hcost : prefixCubeCost N ≤ A/rho^N :=
    (le_div_iff₀ (pow_pos rho_pos N)).mpr (ha N)
  have hNm : (N:ℝ) ≤ m x := by exact_mod_cast hN
  have hp : rho^N*rho^(m x-N)=rho^(m x) := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  calc
    _ ≤ (m x:ℝ)*(A/rho^N)/B x := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul hNm hcost (prefixCubeCost_nonneg N) (Nat.cast_nonneg _)
    _ = A*((m x:ℝ)/(B x*rho^(m x)))*rho^(m x-N) := by
      rw [← hp]
      field_simp [rho_pos.ne']
    _ ≤ A*(2/lam)*rho^(m x-N) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx hA.le) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedGridVolume
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform volume bound for unbanded enlarged prime-prefix grids. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma add_pow_le_exp_ratio {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D) (N : ℕ) :
    (B+D)^N ≤ Real.exp ((N:ℝ)*D/B)*B^N := by
  have hbase : 1+D/B ≤ Real.exp (D/B) := by
    simpa only [add_comm] using Real.add_one_le_exp (D/B)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+D/B) hbase N
  have he : B+D=(1+D/B)*B := by field_simp
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_right hpow (pow_nonneg hB.le N)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime mass in arbitrary nonnegative prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma tupleUnitGrid_cell {N : ℕ} {p : Fin N → ℕ}
    (hp : ∀ i, 0 ≤ primePrefixCoord p i) :
    primePrefixCoord p ∈ unitGridCell (fun i => ⌊primePrefixCoord p i⌋₊+1) := by
  intro i _
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  exact ⟨Nat.floor_le (hp i), Nat.lt_floor_add_one _⟩

lemma tupleUnitGrid_cover {N : ℕ} {Q : Finset (Fin N → ℕ)}
    (hp : ∀ p ∈ Q, ∀ i, (p i).Prime ∧ 0 ≤ primePrefixCoord p i) :
    Q ⊆ gridPrimeTuples (tupleUnitGrid Q) := by
  intro p hpQ
  apply Finset.mem_biUnion.mpr
  refine ⟨(fun i => ⌊primePrefixCoord p i⌋₊+1), Finset.mem_image.mpr ⟨p,hpQ,rfl⟩, ?_⟩
  exact mem_primeBoxTuples_iff.mpr ⟨fun i => (hp p hpQ i).1,
    tupleUnitGrid_cell (fun i => (hp p hpQ i).2)⟩

lemma tupleUnitGrid_positive {N : ℕ} {Q : Finset (Fin N → ℕ)}
    {b : Fin N → ℕ} (hb : b ∈ tupleUnitGrid Q) (i : Fin N) : 1 ≤ b i := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hb
  simp only
  omega

lemma sum_exp_neg_linear_prefix {N : ℕ} {c : ℝ} (hc : 0 < c)
    (b : Fin N → ℕ) (hb : ∀ i, c*(N-i.val:ℕ) ≤ (b i:ℝ)) :
    (∑ i, Real.exp (-(b i:ℝ))) ≤ (1-Real.exp (-c))⁻¹ := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin N, q^(N-i.val-1) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh : ((N-i.val-1:ℕ):ℝ) ≤ (N-i.val:ℕ) := by
        exact_mod_cast Nat.sub_le (N-i.val) 1
      have := mul_le_mul_of_nonneg_left hh hc.le
      linarith [hb i]
    _ = ∑ j ∈ Finset.range N, q^j := by
      apply Finset.sum_bij (fun i _ => N-i.val-1)
      · intro i _
        exact Finset.mem_range.mpr (by omega)
      · intro i _ j _ hij
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
      · intro j hj
        have hj := Finset.mem_range.mp hj
        exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
      · intro i _
        rfl
    _ ≤ ∑' j : ℕ, q^j := hs.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
    _ = _ := tsum_geometric_of_lt_one hq0 hq1

/-- A linear lower envelope is enough for a dimension-independent prime
mass factor; no concentration or band assumption is used. -/
theorem unbanded_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (Q : Finset (Fin N → ℕ)) (c A : ℝ),
      0 < c →
      (∀ p ∈ Q, ∀ i, (p i).Prime ∧ c*(N-i.val:ℕ) ≤ primePrefixCoord p i) →
      ((tupleUnitGrid Q).card:ℝ) ≤ A →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤ Real.exp (C*(1-Real.exp (-c))⁻¹)*A := by
  obtain ⟨C,hC,hgrid⟩ := grid_prime_mass_error_of_sum hford
  refine ⟨C,hC,?_⟩
  intro N Q c A hc hQ hA
  have hp (p) (hpQ : p ∈ Q) (i) : (p i).Prime ∧ 0 ≤ primePrefixCoord p i :=
    ⟨(hQ p hpQ i).1, (mul_nonneg hc.le (Nat.cast_nonneg _)).trans (hQ p hpQ i).2⟩
  have he (b) (hb : b ∈ tupleUnitGrid Q) :
      (∑ i, Real.exp (-(b i:ℝ))) ≤ (1-Real.exp (-c))⁻¹ := by
    apply sum_exp_neg_linear_prefix hc b
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hb
    intro i
    exact (hQ p hpQ i).2.trans (by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (primePrefixCoord p i)).le)
  have hh := (le_abs_self _).trans (hgrid (tupleUnitGrid Q) _
    (fun b hb i => tupleUnitGrid_positive hb i) he)
  calc
    _ ≤ gridPrimeMass (tupleUnitGrid Q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (tupleUnitGrid_cover hp)
        (fun p _ _ => reciprocalShiftWeight_nonneg p)
    _ ≤ Real.exp (C*(1-Real.exp (-c))⁻¹)*(tupleUnitGrid Q).card := by
      nlinarith only [hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordUnbandedMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-prefix mass with Ford's literal row parameters. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma xi_eq_simplexBoxError (x : ℝ) (i : ℕ) :
    xi x i = 1+simplexBoxError 0 (m x-i) := by
  have he : (Real.exp (-(1/40:ℝ)))^(m x-i) =
      Real.exp (-((m x-i:ℕ):ℝ)/40) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold xi simplexBoxError
  rw [he]
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime prefix before a first failed row belongs to the unbanded simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_truncate {K L j : ℕ} (hKL : K ≤ L) (u : ℕ → ℝ)
    (hu : ∀ r, 0 ≤ u r) : fordRowSum K u j ≤ fordRowSum L u j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.trans hKL⟩
  · intro r hr _
    have hr := Finset.mem_Icc.mp hr
    exact mul_nonneg (a_pos (by omega)).le (hu r)

lemma rows_give_enlarged_prefix {K L : ℕ} {x : ℝ} (hKL : K ≤ L)
    (u : ℕ → ℝ) (hu : ∀ r, 0 ≤ u r)
    (hrows : ∀ i ≤ K, fordRowSum L u i ≤ xi x i*(if i=0 then B x else u i)) :
    (fun i : Fin K => u (i.val+1)) ∈
      enlargedSimplex K (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨fun i => hu _,?_,?_⟩
  · intro i
    have hh := (fordRowSum_truncate (j:=i.val+1) hKL u hu).trans
      (hrows (i.val+1) (by have := i.isLt; omega))
    unfold fordRowSum at hh
    rw [prefix_sum_fin] at hh
    simpa only [Fin.lt_def,Nat.add_lt_add_iff_right,Nat.add_sub_add_right,Nat.add_eq_zero_iff,
      Nat.one_ne_zero,and_false,ite_false, if_false] using hh
  · have hh := (fordRowSum_truncate (j:=0) hKL u hu).trans (hrows 0 (Nat.zero_le _))
    unfold fordRowSum at hh
    rw [prefix_sum_fin] at hh
    simpa only [Nat.zero_lt_succ,ite_true, if_true,Nat.sub_zero] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedCoordinateMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime reciprocal mass inherits the fixed-coordinate concentration bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_prime_mass (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ Q : Finset (Fin (N+2) → ℕ),
    (∀ p∈Q,(∀ j,(p j).Prime) ∧
      primePrefixCoord p∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (∀ j,j.val+1=N+2 → (1/100:ℝ) ≤ primePrefixCoord p j) ∧
      (primePrefixCoord p i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primePrefixCoord p i)) →
    (∑ p∈Q,reciprocalShiftWeight p) ≤ 
      C*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,c,hA,hc,hgrid⟩ := fixed_coordinate_grid_bound H
  obtain ⟨d,hd,hlower⟩ := reverse_enlarged_linear_lower
  obtain ⟨D,_hD,hmass⟩ := unbanded_prime_mass_bound fordUnitPrimeBoxInput
  refine ⟨Real.exp (D*(1-Real.exp (-d))⁻¹)*A,c,by positivity,hc,?_⟩
  filter_upwards [hgrid] with P hP
  filter_upwards [hP] with x hx
  intro N hN i hi Q hQ
  have hcoords (p) (hp : p∈Q) : ∀ j,d*(N+2-j.val:ℕ) ≤ primePrefixCoord p j := by
    apply hlower (m x) (N+2) (by omega) (B x) (primePrefixCoord p)
    · simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using (hQ p hp).2.1
    · exact (hQ p hp).2.2.1
  have hcard : ((tupleUnitGrid Q).card:ℝ) ≤ 
      A*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N hN i hi
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨primePrefixCoord p,tupleUnitGrid_cell (fun j => ?_),
      (hQ p hp).2.1,(hQ p hp).2.2.2⟩
    exact (mul_nonneg hd.le (Nat.cast_nonneg _)).trans (hcoords p hp j)
  have hh := hmass Q d _ hd
    (fun p hp j => ⟨(hQ p hp).1 j,hcoords p hp j⟩) hcard
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedTerminalRate
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive uniform terminal-cap rate a fixed distance from the natural dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_rate (H : ℕ) {E : ℝ} (hE : 0 < E) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+H=m x → ∀ κ : ℝ,0 < κ → κ ≤ E →
      c ≤ (N:ℝ)*g N/(κ*(B x+prefixCubeCost N)) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  let L : ℝ := (gamma*rho^H)*rho/(2*lam)
  have hL : 0 < L := div_pos (mul_pos (mul_pos gamma_pos (pow_pos rho_pos H)) rho_pos) (by have := lam_pos; positivity)
  refine ⟨L/(E*(1+A)),by positivity,?_⟩
  have hp := normalized_prefactor_step fordRenewalInput H
  filter_upwards [hcost,hp.eventually (eventually_gt_nhds
    (show (gamma*rho^H)/2 < gamma*rho^H by have := mul_pos gamma_pos (pow_pos rho_pos H); linarith)),theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+1))] with x hcost hp hphase hB hm
  intro N hN
  have hNsub : m x-H=N := by omega
  rw [hNsub] at hp
  have hm' : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc0 : 0 ≤ prefixCubeCost N/B x := div_nonneg (prefixCubeCost_nonneg _) hB.le
  have hc : prefixCubeCost N/B x ≤ A := by
    have hh := (hcost N (by omega)).trans
      (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
    have he : (N:ℝ)*prefixCubeCost N/B x=
        (N:ℝ)*(prefixCubeCost N/B x) := by ring
    rw [he] at hh
    nlinarith only [hm',hc0,hh]
  have hbudget : B x+prefixCubeCost N ≤ (1+A)*B x := by
    have hh := (div_le_iff₀ hB).mp hc
    nlinarith only [hh]
  have hratio0 : 0 ≤ (N:ℝ)*g N/B x :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le) hB.le
  have halpha := mul_le_mul_of_nonneg_right (alpha_le _ hphase) hratio0
  have hratio : L ≤ (N:ℝ)*g N/B x := by
    have hh : (gamma*rho^H)/2 ≤ (lam/rho)*((N:ℝ)*g N/B x) := hp.le.trans halpha
    have hh' : ((gamma*rho^H)/2)/(lam/rho) ≤ (N:ℝ)*g N/B x :=
      (div_le_iff₀ (div_pos lam_pos rho_pos)).mpr (by simpa only [mul_comm] using hh)
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [L]
    field_simp
  have hnumerator := (le_div_iff₀ hB).mp hratio
  intro κ hκ hκE
  apply (le_div_iff₀ (mul_pos hκ (add_pos_of_pos_of_nonneg hB (prefixCubeCost_nonneg _)))).mpr
  have hden : κ*(B x+prefixCubeCost N) ≤ E*((1+A)*B x) :=
    mul_le_mul hκE hbudget (add_nonneg hB.le (prefixCubeCost_nonneg _)) hE.le
  have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ L/(E*(1+A)) by positivity)
  have hid : (L/(E*(1+A)))*(E*((1+A)*B x))=L*B x := by field_simp
  rw [hid] at hh
  exact hh.trans hnumerator

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixTerminalVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal slice of a prefix region is another prefix region. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixLinear_last (N : ℕ) (u : Fin (N+1) → ℝ) :
    prefixLinear (N+1) u (Fin.last N)=u (Fin.last N) := by
  rw [prefixLinear_apply]
  have hz : (∑ j : Fin (N+1),
      if Fin.last N < j then a (j.val-(Fin.last N).val)*u j else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.lt_def,Fin.val_last]; omega)]
  rw [hz,sub_zero]

lemma weighted_sum_update_last (N : ℕ) (C : Fin (N+1) → ℝ) (t : ℝ) :
    (∑ i : Fin (N+1),g (i.val+1)*Function.update C (Fin.last N) t i)=
      (∑ i : Fin (N+1),g (i.val+1)*C i)+g (N+1)*(t-C (Fin.last N)) := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  have hs : (∑ i : Fin N,g (i.castSucc.val+1)*
      Function.update C (Fin.last N) t i.castSucc)=
      ∑ i : Fin N,g (i.castSucc.val+1)*C i.castSucc := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
  rw [hs,Function.update_self]
  simp only [Fin.val_last]
  ring

lemma prefixRegion_terminal_inter (N : ℕ) (B C₀ : ℝ)
    (C : Fin (N+1) → ℝ) {t : ℝ} (ht : C (Fin.last N) ≤ t) :
    prefixRegion (N+1) B C₀ C ∩ {u | t ≤ u (Fin.last N)}=
      prefixRegion (N+1) B C₀ (Function.update C (Fin.last N) t) := by
  ext u
  constructor
  · rintro ⟨⟨hu,hbudget⟩,hterminal⟩
    refine ⟨fun i => ?_,hbudget⟩
    by_cases hi : i=Fin.last N
    · subst i
      rw [Function.update_self,prefixLinear_last]
      exact hterminal
    · rw [Function.update_of_ne hi]
      exact hu i
  · rintro ⟨hu,hbudget⟩
    have hterminal : t ≤ u (Fin.last N) := by
      have hh := hu (Fin.last N)
      rwa [Function.update_self,prefixLinear_last] at hh
    refine ⟨⟨fun i => ?_,hbudget⟩,hterminal⟩
    by_cases hi : i=Fin.last N
    · subst i
      rw [prefixLinear_last]
      exact ht.trans hterminal
    · have hh := hu i
      rwa [Function.update_of_ne hi] at hh

/-- Exact cap volume, including the empty-cap case through the positive part. -/
theorem volume_prefixRegion_terminal (N : ℕ) (B C₀ : ℝ)
    (C : Fin (N+1) → ℝ) {t : ℝ} (ht : C (Fin.last N) ≤ t) :
    volume (prefixRegion (N+1) B C₀ C ∩ {u | t ≤ u (Fin.last N)})=
      ENNReal.ofReal
        ((max (B-C₀-(∑ i : Fin (N+1),g (i.val+1)*C i)-
            g (N+1)*(t-C (Fin.last N))) 0)^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  rw [prefixRegion_terminal_inter N B C₀ C ht,
    volume_prefixRegion_explicit (N+1) (by omega),weighted_sum_update_last]
  congr 1
  congr 2
  congr 1
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexTerminalCap
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact terminal-coordinate slice of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplex_cap_power_bound {B t : ℝ} (hB : 0 < B) (_ht : 0 ≤ t)
    (htB : t ≤ B) (N : ℕ) :
    (B-t)^N ≤ Real.exp (-(N:ℝ)*t/B)*B^N := by
  have hbase : 1-t/B ≤ Real.exp (-t/B) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using (Real.add_one_le_exp (-(t/B)))
  have hbase0 : 0 ≤ 1-t/B := by
    have hh := (div_le_one hB).mpr htB
    linarith only [hh]
  have hp := pow_le_pow_left₀ hbase0 hbase N
  have he : B-t=(1-t/B)*B := by field_simp
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_right hp (pow_nonneg hB.le N)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- The exponential bound also covers caps beyond the whole simplex. -/
lemma simplex_positive_part_power_bound {B t : ℝ} (hB : 0 < B) (ht : 0 ≤ t)
    {N : ℕ} (hN : 0 < N) :
    (max (B-t) 0)^N ≤ Real.exp (-(N:ℝ)*t/B)*B^N := by
  by_cases htB : t ≤ B
  · rw [max_eq_left (sub_nonneg.mpr htB)]
    exact simplex_cap_power_bound hB ht htB N
  · rw [max_eq_right (by linarith only [not_le.mp htB]),zero_pow hN.ne']
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedTerminalCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal lower bound survives unit-box thickening with its exact cost. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem unbanded_grid_terminal_volume_bound (N : ℕ)
    (B β₀ t : ℝ) (β κ : Fin (N+1) → ℝ) (K : Finset (Fin (N+1) → ℕ))
    (hβ₀ : 0 < β₀) (hβ : ∀ i,0 < β i) (ht : 0 ≤ t)
    (hκ : ∀ i,1 ≤ κ i) (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    (hK : ∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) B β₀ β ∧ t ≤ u (Fin.last N)) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      ((max (B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N))) 0)^(N+1)/
        (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  let C : Fin (N+1) → ℝ := fun i => -((N+1-i.val:ℕ):ℝ)^2
  let S := prefixRegion (N+1) (B+(N+1:ℝ)^2) 0 C ∩
    {u | t/κ (Fin.last N)-1 ≤ u (Fin.last N)}
  have hκpos (i) : 0 < κ i := zero_lt_one.trans_le (hκ i)
  have hp : 0 < ∏ i,κ i := Finset.prod_pos (fun i _ => hκpos i)
  have hd : LinearMap.det (simplexScale κ)≠0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hsub : gridRegion K ⊆ simplexScale κ ⁻¹' S := by
    intro v hv
    obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hub,hu,hterminal⟩ := hK b hb
    have hdist := simplexScale_unit_distance hκ (unitGridCell_coordinate_distance hub hvb)
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,C] using prefixRegion_unit_cube
        (enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu) hdist
    · have ht' := div_le_div_of_nonneg_right hterminal (hκpos (Fin.last N)).le
      have hd' := (abs_le.mp (hdist (Fin.last N))).2
      rw [simplexScale_apply] at hd'
      change t/κ (Fin.last N)-1 ≤ simplexScale κ v (Fin.last N)
      linarith only [ht',hd']
  have hS : MeasurableSet S :=
    (measurableSet_prefixRegion _ _ _ _).inter
      (measurableSet_le measurable_const (measurable_pi_apply _))
  have hvol : volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*volume S := by
    apply (measure_mono hsub).trans_eq
    rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hS,
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd,simplexScale_det,
      inv_inv,abs_of_pos hp,Measure.smul_apply,smul_eq_mul]
  have hC : C (Fin.last N)= -1 := by simp [C]
  have hthreshold : C (Fin.last N) ≤ t/κ (Fin.last N)-1 := by
    rw [hC]
    have hh := div_nonneg ht (hκpos (Fin.last N)).le
    linarith only [hh]
  have hformula := volume_prefixRegion_terminal N (B+(N+1:ℝ)^2) 0 C hthreshold
  have hbudget : B+(N+1:ℝ)^2-0-(∑ i : Fin (N+1),g (i.val+1)*C i)-
      g (N+1)*(t/κ (Fin.last N)-1-C (Fin.last N))=
      B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N)) := by
    rw [hC]
    simp only [C,prefixCubeCost,mul_neg,Finset.sum_neg_distrib,Nat.cast_add,Nat.cast_one]
    ring
  rw [hbudget] at hformula
  change volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*
    volume (prefixRegion (N+1) (B+(N+1:ℝ)^2) 0 C ∩
      {u | t/κ (Fin.last N)-1 ≤ u (Fin.last N)}) at hvol
  rw [hformula,← ENNReal.ofReal_mul hp.le] at hvol
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have hden : 0 ≤ (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (g_pos _).le))
  have hnresult : 0 ≤ (∏ i,κ i)*
      ((max (B+prefixCubeCost (N+1)-g (N+1)*(t/κ (Fin.last N))) 0)^(N+1)/
        (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) :=
    mul_nonneg hp.le (div_nonneg (pow_nonneg (le_max_right _ _) _) hden)
  simpa only [gridRegion_volume_real,ENNReal.toReal_ofReal hnresult] using hh

theorem unbanded_grid_terminal_exponential (N : ℕ)
    (B β₀ t : ℝ) (β κ : Fin (N+1) → ℝ) (K : Finset (Fin (N+1) → ℕ))
    (hB : 0 < B) (hβ₀ : 0 < β₀) (hβ : ∀ i,0 < β i) (ht : 0 ≤ t)
    (hκ : ∀ i,1 ≤ κ i) (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    (hK : ∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) B β₀ β ∧ t ≤ u (Fin.last N)) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      (Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
          (B+prefixCubeCost (N+1)))*
        (B+prefixCubeCost (N+1))^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  apply (unbanded_grid_terminal_volume_bound N B β₀ t β κ K hβ₀ hβ ht hκ htop hstep hK).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => (hκ i).trans' zero_le_one))
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (g_pos _).le)))
  exact simplex_positive_part_power_bound
    (add_pos_of_pos_of_nonneg hB (prefixCubeCost_nonneg _))
    (mul_nonneg (g_pos _).le (div_nonneg ht (zero_le_one.trans (hκ _)))) (by omega)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedTerminalGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponentially decaying prime-prefix grid counts a fixed distance from the natural dimension. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_grid_bound (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+1+H=m x → ∀ t : ℝ,0 ≤ t →
    ∀ K : Finset (Fin (N+1) → ℕ),
    (∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) (B x) (1+simplexBoxError 0 (m x))
        (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) ∧ t ≤ u (Fin.last N)) →
    (K.card:ℝ) ≤ C*G x (N+1)*Real.exp (-c*t) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  let E := Real.exp (∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n)
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨c,hc,hrate⟩ := fixed_terminal_rate H hE
  refine ⟨E*Real.exp A,c,by positivity,hc,?_⟩
  filter_upwards [hcost,hrate,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hcost hrate hB
  intro N hNm t ht K hK
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m x-r)
  let κ : Fin (N+1) → ℝ := enlargementScale β
  have hβ (r) : 1 ≤ β r := by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m x-r)]
  have hκ (i) : 1 ≤ κ i := (hβ 0).trans (enlargementScale_top hβ i)
  have hκE (i) : κ i ≤ E := by
    have hh := reverse_enlargement_coordinate (m:=m x) (H:=0)
      (Nat.zero_le (m x)) (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
      (summable_simplexBoxError_weighted 0) i (by have := i.isLt; omega)
    simpa only [Nat.zero_add] using hh
  have hj : (∏ i,κ i) ≤ E := by
    have hh := reverse_enlargement_jacobian (m:=N+1+H) (P:=H) (by omega)
      (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
      (summable_simplexBoxError_weighted 0)
    rw [Nat.add_sub_cancel] at hh
    have ht : (∑' n : ℕ,((H+n:ℕ):ℝ)*simplexBoxError 0 (H+n)) ≤
        ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by
      have hs := summable_simplexBoxError_weighted 0
      have he := hs.sum_add_tsum_nat_add H
      have hn : 0 ≤ ∑ n ∈ Finset.range H,(n:ℝ)*simplexBoxError 0 n :=
        Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (simplexBoxError_nonneg (by norm_num) n))
      have ht' : (∑' n : ℕ,((n+H:ℕ):ℝ)*simplexBoxError 0 (n+H)) ≤
          ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by linarith only [he,hn]
      simpa only [Nat.add_comm] using ht'
    have hh' : (∏ i,κ i) ≤ Real.exp (∑' n : ℕ,((H+n:ℕ):ℝ)*simplexBoxError 0 (H+n)) := by
      simpa only [κ,β,← hNm] using hh
    exact hh'.trans (Real.exp_le_exp.mpr ht)
  have hvol := unbanded_grid_terminal_exponential N (B x) (β 0) t
    (fun i => β (i.val+1)) κ K hB (zero_lt_one.trans_le (hβ 0))
    (fun i => zero_lt_one.trans_le (hβ (i.val+1))) ht hκ
    (enlargementScale_top hβ) (enlargementScale_step hβ) hK
  have hrate' := hrate (N+1) hNm (κ (Fin.last N)) (zero_lt_one.trans_le (hκ _)) (hκE _)
  have hexp : Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
      (B x+prefixCubeCost (N+1))) ≤ Real.exp (-c*t) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hrate' ht
    have he : -((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1))=
        -(((N+1:ℕ):ℝ)*g (N+1)/(κ (Fin.last N)*(B x+prefixCubeCost (N+1))))*t := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    linarith only [hh]
  have hr : ((N+1:ℕ):ℝ)*prefixCubeCost (N+1)/B x ≤ A := by
    have hh := hcost (N+1) (by omega)
    exact hh.trans (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hp := (add_pow_le_exp_ratio hB (prefixCubeCost_nonneg (N+1)) (N+1)).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hr) (pow_nonneg hB.le _))
  have hden : 0 < (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  have hmain : (∏ i,κ i)*((B x+prefixCubeCost (N+1))^(N+1)/
      (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) ≤
      (E*Real.exp A)*G x (N+1) := by
    calc
      _ ≤ E*(Real.exp A*(B x)^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
        apply mul_le_mul hj (div_le_div_of_nonneg_right hp hden.le)
          (div_nonneg (pow_nonneg (add_nonneg hB.le (prefixCubeCost_nonneg _)) _) hden.le) hE.le
      _ = _ := by rw [G,prod_fin_shifted (N+1) g]; ring
  calc
    _ ≤ (∏ i,κ i)*(Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1)))*(B x+prefixCubeCost (N+1))^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := hvol
    _ = Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1)))*((∏ i,κ i)*
          ((B x+prefixCubeCost (N+1))^(N+1)/
            (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)))) := by ring
    _ ≤ Real.exp (-c*t)*((E*Real.exp A)*G x (N+1)) :=
      mul_le_mul hexp hmain
        (mul_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hκ i)))
          (div_nonneg (pow_nonneg (add_nonneg hB.le (prefixCubeCost_nonneg _)) _) hden.le))
        (Real.exp_pos _).le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedTerminalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal cap persists for actual reciprocal shifted-prime mass. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_prime_mass (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+1+H=m x → ∀ t : ℝ,0 ≤ t →
    ∀ Q : Finset (Fin (N+1) → ℕ),
    (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
      primePrefixCoord p ∈ enlargedSimplex (N+1) (B x)
        (1+simplexBoxError 0 (m x))
        (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) ∧
      (1/100:ℝ) ≤ primePrefixCoord p (Fin.last N) ∧
      t ≤ primePrefixCoord p (Fin.last N)) →
    (∑ p ∈ Q,reciprocalShiftWeight p) ≤ C*G x (N+1)*Real.exp (-c*t) := by
  obtain ⟨A,c,hA,hc,hgrid⟩ := fixed_terminal_grid_bound H
  obtain ⟨d,hd,hlower⟩ := reverse_enlarged_linear_lower
  obtain ⟨D,hD,hmass⟩ := unbanded_prime_mass_bound fordUnitPrimeBoxInput
  refine ⟨Real.exp (D*(1-Real.exp (-d))⁻¹)*A,c,by positivity,hc,?_⟩
  filter_upwards [hgrid] with x hx
  intro N hN t ht Q hQ
  have hcoords (p) (hp : p ∈ Q) : ∀ i,d*(N+1-i.val:ℕ) ≤ primePrefixCoord p i := by
    apply hlower (m x) (N+1) (by omega) (B x) (primePrefixCoord p) (hQ p hp).2.1
    intro i hi
    have he : i=Fin.last N := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [he] using (hQ p hp).2.2.1
  have hcard : ((tupleUnitGrid Q).card:ℝ) ≤ A*G x (N+1)*Real.exp (-c*t) := by
    apply hx N hN t ht
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨primePrefixCoord p,tupleUnitGrid_cell (fun i => ?_),(hQ p hp).2.1,(hQ p hp).2.2.2⟩
    exact (mul_nonneg hd.le (Nat.cast_nonneg _)).trans (hcoords p hp i)
  have hh := hmass Q d (A*G x (N+1)*Real.exp (-c*t)) hd
    (fun p hp i => ⟨(hQ p hp).1 i,hcoords p hp i⟩) hcard
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedCoordinateTerminalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine coordinate concentration with terminal decay so that the smooth
residuals can still be summed over all terminal strips. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma two_exponential_bounds {R Z A B u v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hu : R ≤ A*Z*Real.exp u) (hv : R ≤ B*Z*Real.exp v) :
    R ≤ (A+B)*Z*Real.exp ((u+v)/2) := by
  by_cases huv : u ≤ v
  · apply hu.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hZ
    · exact Real.exp_le_exp.mpr (by linarith only [huv])
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (add_nonneg hA hB) hZ
  · apply hv.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hZ
    · exact Real.exp_le_exp.mpr (by linarith only [huv])
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (add_nonneg hA hB) hZ

theorem fixed_coordinate_terminal_mass (H : ℕ) :
    ∃ C a c : ℝ,0 < C ∧ 0 < a ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ t : ℝ,0 ≤ t → ∀ Q : Finset (Fin (N+2) → ℕ),
    (∀ p∈Q,(∀ j,(p j).Prime) ∧
      primePrefixCoord p∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (1/100:ℝ) ≤ primePrefixCoord p (Fin.last (N+1)) ∧
      t ≤ primePrefixCoord p (Fin.last (N+1)) ∧
      (primePrefixCoord p i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primePrefixCoord p i)) →
    (∑ p∈Q,reciprocalShiftWeight p) ≤ C*G x (N+2)*
      Real.exp (-a*t-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,a,hA,ha,htail⟩ := fixed_terminal_prime_mass H
  obtain ⟨B,c,hB,hc,hcoord⟩ := fixed_coordinate_prime_mass H
  refine ⟨A+B,a/2,c/2,add_pos hA hB,by positivity,by positivity,?_⟩
  filter_upwards [hcoord] with P hP
  filter_upwards [hP,htail,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx ht hBx
  intro N hN i hi t ht0 Q hQ
  have h1 := ht (N+1) (by omega) t ht0 Q (by
    intro p hp
    exact ⟨(hQ p hp).1,by
      simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using (hQ p hp).2.1,
      (hQ p hp).2.2.1,(hQ p hp).2.2.2.1⟩)
  have h2 := hx N hN i hi Q (by
    intro p hp
    refine ⟨(hQ p hp).1,(hQ p hp).2.1,?_,(hQ p hp).2.2.2.2⟩
    intro j hj
    have he : j=Fin.last (N+1) := by apply Fin.ext; simp only [Fin.val_last]; omega
    simpa only [he] using (hQ p hp).2.2.1)
  have hh := two_exponential_bounds hA.le hB.le (G_pos hBx (N+2)).le h1 h2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmallTerminalPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded terminal coordinate supplies an exact smooth residual split. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma terminal_prefix_conditions {x t : ℝ} {n L j : ℕ}
    (hj : 2 ≤ j) (hjL : j ≤ L) (ht : (1/100:ℝ) ≤ t)
    (hprev : t < fordPrimeCoordinate n (j-1))
    (hrows : ∀ i < j,fordRowSum L (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i)) :
    (∀ i,(fordPrefixPrimes n (j-1) i).Prime) ∧
    primePrefixCoord (fordPrefixPrimes n (j-1)) ∈
      enlargedSimplex (j-1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
    (∀ i,i.val+1=j-1 → (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes n (j-1)) i) := by
  have hp (i : Fin (j-1)) : 0 < fordPrimeCoordinate n (i.val+1) := by
    have ho := ford_coordinate_antitone n (show i.val+1 ≤ j-1 by omega)
    linarith only [ho,hprev,ht]
  have he : primePrefixCoord (fordPrefixPrimes n (j-1))=
      fun i : Fin (j-1) => fordPrimeCoordinate n (i.val+1) := by
    funext i
    exact (fordPrimeCoordinate_eq_raw_of_pos (hp i)).symm
  refine ⟨fun i => fordPrime_prime (fordPrime_index_of_doubleLog_pos
    (by rw [← fordPrimeCoordinate_eq_raw_of_pos (hp i)]; exact hp i)),?_,?_⟩
  · rw [he]
    exact rows_give_enlarged_prefix (by omega) _ (fun _ => le_max_left _ _)
      (fun i hi => hrows i (by omega))
  · intro i hi
    rw [he]
    change (1/100:ℝ) ≤ fordPrimeCoordinate n (i.val+1)
    rw [hi]
    linarith only [ht,hprev]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPowerBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary logarithmic budgets at a power-four-thirds threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_square_quarter_bound {b : ℝ} (hb : 1 ≤ b) :
    (Real.log (b+4))^2 ≤ 320*b^(1/4:ℝ) := by
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (show 0 ≤ b+4 by linarith)
    (by norm_num : (0:ℝ)<1/8)
  have hq : ((b+4)^(1/8:ℝ))^2=(b+4)^(1/4:ℝ) := by
    rw [pow_two,← Real.rpow_add (by linarith : 0 < b+4)]
    norm_num
  have hp := Real.rpow_nonneg (show 0 ≤ b+4 by linarith) (1/8:ℝ)
  have hs : (Real.log (b+4))^2 ≤ 64*(b+4)^(1/4:ℝ) := by
    norm_num at hlog
    nlinarith only [hlog,hq,hl,hp]
  have ht : (b+4)^(1/4:ℝ) ≤ 5*b^(1/4:ℝ) := by
    calc
      _ ≤ (5*b)^(1/4:ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = (5:ℝ)^(1/4:ℝ)*b^(1/4:ℝ) := Real.mul_rpow (by norm_num) hb0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤5) (by norm_num))
        (Real.rpow_nonneg hb0.le _)
  linarith only [hs,ht]

lemma logarithm_budget_quarter_bound {b F : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) :
    100*(Real.log (b+4)+F+30)^2 ≤ (10000*(F+31)^2)*b^(1/4:ℝ) := by
  have hlog := logarithm_square_quarter_bound hb
  have hs := Real.one_le_rpow hb (by norm_num : (0:ℝ)≤1/4)
  have hsum : (Real.log (b+4)+F+30)^2 ≤ 2*(Real.log (b+4))^2+2*(F+30)^2 := by
    nlinarith only [sq_nonneg (Real.log (b+4)-(F+30))]
  have hc : 64000+200*(F+30)^2 ≤ 10000*(F+31)^2 := by
    nlinarith only [hF,sq_nonneg F]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (F+30))
  have hfinal := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith : 0 ≤ b) (1/4:ℝ))
  nlinarith only [hlog,hsum,hmul,hfinal]

lemma four_thirds_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b := by
  have hb0 : 0 < b := by linarith
  have hK : 0 ≤ 10000*(F+31)^2 := by positivity
  have hs : (10000*(F+31)^2)/δ ≤ b^(3/4:ℝ) := by
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (div_nonneg hK hδ.le) (4/3:ℝ)) hthreshold
      (by norm_num : (0:ℝ)≤3/4)
    rw [← Real.rpow_mul (div_nonneg hK hδ.le)] at hh
    norm_num at hh
    exact hh
  have hc : 10000*(F+31)^2 ≤ δ*b^(3/4:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hb0.le (1/4:ℝ))
  have he : δ*b^(3/4:ℝ)*b^(1/4:ℝ)=δ*b := by
    rw [mul_assoc,← Real.rpow_add hb0]
    norm_num
  exact (logarithm_budget_quarter_bound hb hF).trans (by simpa only [he] using hm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalMassSeries
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth residual mass is summable against terminal-coordinate decay. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma terminalMassWeight_pos (c : ℝ) (k : ℕ) : 0 < terminalMassWeight c k := Real.exp_pos _

theorem summable_terminalMassWeight {c : ℝ} (hc : 0 < c) :
    Summable (terminalMassWeight c) := by
  let q := Real.exp (-c/2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded_eventually_nat
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ))),
    eventually_ge_atTop (1:ℕ)] with k hk hk1
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hb : 1 ≤ (k:ℝ)+1 := by linarith only [hk0]
  have hthreshold : ((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ) ≤ (k:ℝ)+1 := by
    linarith only [hk]
  have hbudget := four_thirds_threshold_budget hb (le_refl (0:ℝ))
    (show 0 < c/4 by linarith only [hc]) hthreshold
  have hlog : 0 ≤ Real.log ((k:ℝ)+5) := Real.log_nonneg (by linarith only [hk0])
  have he : 10*(Real.log ((k:ℝ)+5))^2-c*k ≤ -(c/2)*(k:ℝ) := by
    simp only [add_zero] at hbudget
    rw [show (k:ℝ)+1+4=(k:ℝ)+5 by ring] at hbudget
    have hh : c/4*((k:ℝ)+1) ≤ (c/2)*(k:ℝ) := by nlinarith only [hc,hk0]
    nlinarith only [hbudget,hh,hlog,sq_nonneg (Real.log ((k:ℝ)+5))]
  rw [Real.norm_eq_abs,abs_of_pos (terminalMassWeight_pos c k)]
  dsimp only [terminalMassWeight,q]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith only [he]

lemma finite_terminal_mass_bound {c : ℝ} (hc : 0 < c) (I : Finset ℕ) :
    (∑ k ∈ I,terminalMassWeight c k) ≤ ∑' k : ℕ,terminalMassWeight c k :=
  (summable_terminalMassWeight hc).sum_le_tsum _ (fun k _ => (terminalMassWeight_pos c k).le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedCoordinateValueStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed bad coordinate remains exponentially rare when distinct smooth
residual totients are attached to a terminal prime-prefix strip. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_value_strip (H : ℕ) :
    ∃ C a c : ℝ,0 < C ∧ 0 < a ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+3+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ k : ℕ,2 ≤ k → ∀ Q : Finset ℕ,∀ n : ℕ→ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      N+3 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
      ∀ j < N+3,fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤ 
        xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
    (∀ v∈Q,(k:ℝ) ≤ fordPrimeCoordinate (n v) (N+3) ∧
      fordPrimeCoordinate (n v) (N+3) ≤ (k:ℝ)+1) →
    (∀ v∈Q,primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
      (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*
      Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,a,c,hA,ha,hc,hmass⟩ := fixed_coordinate_terminal_mass (H+1)
  obtain ⟨D,hD,hcount⟩ := terminal_prefix_mass_count
  refine ⟨D*A,a,c,mul_pos hD hA,ha,hc,?_⟩
  filter_upwards [hmass] with P hP
  filter_upwards [hP,hcount,eventually_gt_atTop (1:ℝ)] with x hx hcount hx1
  intro N hN i hi k hk Q n hQ hstrip hbad
  let Z:=Q.image (fun v => fordPrefixPrimes (n v) (N+2))
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hpre (v) (hv : v∈Q) :
      (∀ j,(fordPrefixPrimes (n v) (N+2) j).Prime) ∧
      primePrefixCoord (fordPrefixPrimes (n v) (N+2))∈
        enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes (n v) (N+2)) (Fin.last (N+1)) := by
    have ho := ford_coordinate_antitone (n v) (show N+2 ≤ N+3 by omega)
    have hprev : 1 < fordPrimeCoordinate (n v) (N+2) := by
      linarith only [ho,(hstrip v hv).1,hk']
    have hh := terminal_prefix_conditions (j:=N+3) (L:=N+3) (by omega) le_rfl
      (by norm_num : (1/100:ℝ) ≤ 1) hprev (hQ v hv).2.2.2.2.2.2
    exact ⟨hh.1,hh.2.1,hh.2.2 (Fin.last (N+1)) (by simp)⟩
  have hlast (v) (hv : v∈Q) :
      primePrefixCoord (fordPrefixPrimes (n v) (N+2)) (Fin.last (N+1))=
        fordPrimeCoordinate (n v) (N+2) := by
    have ho := ford_coordinate_antitone (n v) (show N+2 ≤ N+3 by omega)
    have hp : 0 < fordPrimeCoordinate (n v) (N+2) := by
      linarith only [ho,(hstrip v hv).1,hk']
    exact (fordPrimeCoordinate_eq_raw_of_pos hp).symm
  have hm : (∑ p∈Z,reciprocalShiftWeight p) ≤ A*G x (N+2)*
      Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N (by omega) i hi k (by positivity) Z
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(hpre v hv).1,(hpre v hv).2.1,(hpre v hv).2.2,?_,hbad v hv⟩
    rw [hlast v hv]
    exact (hstrip v hv).1.trans (ford_coordinate_antitone (n v) (by omega))
  have hh := hcount (N+2) k Q n (by
    intro v hv
    obtain ⟨hn,hφ,hhead,hvx,hlen,hgap,_hrows⟩ := hQ v hv
    exact ⟨hn,hφ,hhead,hvx,hlen,hgap,(hstrip v hv).2⟩)
  have hnorm : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (mul_nonneg hD.le hnorm))
    (Real.exp_pos (10*(Real.log ((k:ℝ)+5))^2)).le
  have he : Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ))*
      Real.exp (10*(Real.log ((k:ℝ)+5))^2) =
      terminalMassWeight a k*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    unfold terminalMassWeight
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  apply hh.trans
  apply hs.trans_eq
  change D*(x/Real.log x)*(A*G x (N+2)*Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ)))*
    Real.exp (10*(Real.log ((k:ℝ)+5))^2)=_
  calc
    _ = D*A*(x/Real.log x)*G x (N+2)*
        (Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ))*Real.exp (10*(Real.log ((k:ℝ)+5))^2)) := by ring
    _ = _ := by rw [he]; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFixedCoordinateValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the fixed-coordinate strip estimate over the actual floor partition
of the terminal coordinate. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- Distinct values with one fixed bad coordinate retain the exponential
saving after all terminal-coordinate strips have been summed. -/
theorem ppt_fixed_coordinate_value_count (H : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, N+3+H=m x → ∀ i : Fin (N+2), P ≤ m x-(i.val+1) →
      ∀ Q : Finset ℕ, ∀ n : ℕ→ℕ,
      (∀ v∈Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        N+3 ≤ (n v).primeFactorsList.length ∧
        fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
        2 < fordPrimeCoordinate (n v) (N+3) ∧
        ∀ j < N+3, fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤
          xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
      (∀ v∈Q, primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1)) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*
        Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  classical
  obtain ⟨A,a,c,hA,ha,hc,hcount⟩ := fixed_coordinate_value_strip H
  let T := ∑' k : ℕ, terminalMassWeight a k
  have hT : 0 ≤ T := tsum_nonneg (fun k => (terminalMassWeight_pos a k).le)
  refine ⟨A*(T+1),c,by positivity,hc,?_⟩
  filter_upwards [hcount] with P hP
  filter_upwards [hP,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm i hi Q n hQ hbad
  let key : ℕ→ℕ := fun v => ⌊fordPrimeCoordinate (n v) (N+3)⌋₊
  let I := Q.image key
  let R (k : ℕ) := Q.filter (fun v => key v=k)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨key v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
      Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ k∈I,((R k).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  let E := Real.exp (-c*(N+2-(i.val+1):ℕ))
  have hrow (k : ℕ) (hk : k∈I) : ((R k).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*E := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    have hk2 : 2 ≤ key v := Nat.le_floor (hQ v hv).2.2.2.2.2.2.1.le
    apply hx N hNm i hi (key v) hk2 (R (key v)) n
    · intro w hw
      have hwQ := (Finset.mem_filter.mp hw).1
      obtain ⟨hn,hphi,hhead,hwx,hlen,hgap,_hlarge,hrows⟩ := hQ w hwQ
      exact ⟨hn,hphi,hhead,hwx,hlen,hgap,hrows⟩
    · intro w hw
      obtain ⟨hwQ,hkey⟩ := Finset.mem_filter.mp hw
      constructor
      · rw [←hkey]
        exact Nat.floor_le (le_max_left _ _)
      · rw [←hkey]
        exact (Nat.lt_floor_add_one _).le
    · intro w hw
      exact hbad w (Finset.mem_filter.mp hw).1
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+2)*E := by
    have hlog := Real.log_pos hx1
    have hG := G_pos hB (N+2)
    have hE : 0 < E := Real.exp_pos _
    positivity
  calc
    _ ≤ ∑ k∈I,((R k).card:ℝ) := hcard
    _ ≤ ∑ k∈I,A*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*E :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+2)*E)*(∑ k∈I,terminalMassWeight a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (A*(x/Real.log x)*G x (N+2)*E)*T :=
      mul_le_mul_of_nonneg_left (finite_terminal_mass_bound ha I) hfac
    _ ≤ (A*(x/Real.log x)*G x (N+2)*E)*(T+1) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = _ := by dsimp only [E] <;> ring

/-- Sum the reversed-coordinate exponential weights, retaining the exact
fixed terminal loss in the constant. -/
lemma ppt_fixed_coordinate_exponential_sum {N H P m : ℕ} {c : ℝ}
    (hc : 0 < c) (hm : N+3+H=m) (hP : H+1 ≤ P)
    (I : Finset (Fin (N+2))) (hI : ∀ i∈I,P ≤ m-(i.val+1)) :
    (∑ i∈I,Real.exp (-c*(N+2-(i.val+1):ℕ))) ≤
      (Real.exp (c*(H+1:ℕ))/ (1-Real.exp (-c)))*Real.exp (-c*(P:ℝ)) := by
  classical
  let K := P-(H+1)
  let f : Fin (N+2)→ℕ := fun i => N+2-(i.val+1)
  have hinj : Set.InjOn f (I : Set (Fin (N+2))) := by
    intro i _ j _ hij
    apply Fin.ext
    have hi:=i.isLt
    have hj:=j.isLt
    dsimp only [f] at hij
    omega
  have hsub : I.image f ⊆ Finset.Ico K (N+2) := by
    intro r hr
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hr
    have hh:=hI i hi
    have hil:=i.isLt
    dsimp only [K,f]
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hrewrite (r : ℕ) : Real.exp (-c*(r:ℝ))=Real.exp (-c)^r := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hbound : (∑ i∈I,Real.exp (-c*(f i:ℝ))) ≤
      Real.exp (-c*(K:ℝ))/(1-Real.exp (-c)) := by
    calc
      _ = ∑ r∈I.image f,Real.exp (-c*(r:ℝ)) := (Finset.sum_image hinj).symm
      _ ≤ ∑ r∈Finset.Ico K (N+2),Real.exp (-c*(r:ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>(Real.exp_pos _).le)
      _ = ∑ r∈Finset.Ico K (N+2),Real.exp (-c)^r := by simp_rw [hrewrite]
      _ ≤ Real.exp (-c)^K/(1-Real.exp (-c)) :=
        geom_sum_Ico_le_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (by linarith only [hc]))
      _ = _ := by rw [←hrewrite]
  apply hbound.trans_eq
  have hK : (K:ℝ)=(P:ℝ)-(H+1:ℕ) := by
    dsimp only [K]
    exact Nat.cast_sub hP
  rw [hK]
  have he : -c*((P:ℝ)-(H+1:ℕ))=c*(H+1:ℕ)+(-c*(P:ℝ)) := by ring
  rw [he,Real.exp_add]
  ring

/-- A finite family with some bad retained coordinate has exponentially
small cardinality, uniformly after the fixed terminal cutoff. -/
theorem ppt_fixed_bad_coordinate_value_count_oai (H : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, N+3+H=m x → ∀ Q : Finset ℕ, ∀ n : ℕ→ℕ,
      (∀ v∈Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        N+3 ≤ (n v).primeFactorsList.length ∧
        fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
        2 < fordPrimeCoordinate (n v) (N+3) ∧
        ∀ j < N+3,fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤
          xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
      (∀ v∈Q,∃ j∈Finset.Icc 1 (m x-P),
        primeDoubleLog (n v) j < (19/20:ℝ)*fordBandScale x j ∨
          (21/20:ℝ)*fordBandScale x j < primeDoubleLog (n v) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*Real.exp (-c*(P:ℝ)) := by
  classical
  obtain ⟨A,c,hA,hc,hcount⟩:=ppt_fixed_coordinate_value_count H
  let D:=Real.exp (c*(H+1:ℕ))/(1-Real.exp (-c))
  have hD : 0 < D := by
    have hh : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
    exact div_pos (Real.exp_pos _) (sub_pos.mpr hh)
  refine ⟨A*D,c,mul_pos hA hD,hc,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (H+1)] with P hP hPH
  filter_upwards [hP,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm Q n hQ hbad
  let I := Finset.univ.filter (fun i : Fin (N+2) => P ≤ m x-(i.val+1))
  let R (i : Fin (N+2)) := Q.filter (fun v =>
    primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
      (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1))
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨j,hj,hbj⟩:=hbad v hv
    have hj':=Finset.mem_Icc.mp hj
    let i : Fin (N+2):=⟨j-1,by omega⟩
    have hij : i.val+1=j := by dsimp only [i]; omega
    have hi : P ≤ m x-(i.val+1) := by rw [hij]; omega
    have hbi : primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1) := by
      simpa only [hij] using hbj
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
      Finset.mem_filter.mpr ⟨hv,hbi⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ i∈I,((R i).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (i) (hi : i∈I) : ((R i).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N hNm i (Finset.mem_filter.mp hi).2 (R i) n
    · intro v hv
      exact hQ v (Finset.mem_filter.mp hv).1
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+2) := by
    have hlog:=Real.log_pos hx1
    have hG:=G_pos hB (N+2)
    positivity
  calc
    _ ≤ ∑ i∈I,((R i).card:ℝ) := hcard
    _ ≤ ∑ i∈I,A*(x/Real.log x)*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+2))*(∑ i∈I,Real.exp (-c*(N+2-(i.val+1):ℕ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (A*(x/Real.log x)*G x (N+2))*(D*Real.exp (-c*(P:ℝ))) :=
      mul_le_mul_of_nonneg_left (ppt_fixed_coordinate_exponential_sum hc hNm hPH I
        (fun i hi=>(Finset.mem_filter.mp hi).2)) hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.ppt_fixed_bad_coordinate_value_count_oai := @OAI.TotientAsymptotic.ppt_fixed_bad_coordinate_value_count_oai
