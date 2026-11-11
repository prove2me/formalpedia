-- Prove2me | solution 1 for OAI.TotientAsymptotic.local_regular_prime_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:02.467025+00:00
-- url     : https://prove2.me/submissions/8208f9c9-6d2b-4b46-83ab-17b0bd2fd93b

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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_fordLemma26Input
import Theorems.Thm_OAI_TotientAsymptotic_geometric_initial_mass_le_base
import Theorems.Thm_OAI_TotientAsymptotic_locally_concentrated_volume_lower

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

lemma prefixVector_extend (N : ℕ) (u : Fin N → ℝ) :
    prefixVector N (extendPrefix N u) = u := by
  funext i
  simp [prefixVector, extendPrefix]

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorShellDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor envelope is absorbed by every polynomial-geometric shell tail. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma polynomialGeometricTail_tendsto (k : ℕ) (r : ℝ) :
    Tendsto (polynomialGeometricTail k r) atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, ((H+n : ℕ) : ℝ)^k*r^(H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (fun n : ℕ => (n : ℝ)^k*r^n))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete renewal bounds needed for the manuscript's collision cutoff.
These are proved from the defining series; no additional numerical input is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

private lemma small_log_identities :
    Real.log 4 = 2*Real.log 2 ∧ Real.log 6 = Real.log 2+Real.log 3 ∧
    Real.log 8 = 3*Real.log 2 ∧ Real.log 9 = 2*Real.log 3 := by
  refine ⟨Real.log_four_eq, ?_, ?_, ?_⟩
  · convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (2 : ℝ) 3 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (3 : ℝ) 2 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

private lemma log_seven_bounds :
    3*Real.log 2-1/7 ≤ Real.log 7 ∧ Real.log 7 ≤ 3*Real.log 2-1/8 := by
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<7/8)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<8/7)
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hu
  rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hl
  constructor <;> linarith

private lemma renewal_tail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑' n : ℕ, a (n+k+1)*r^(n+k+1)) ≤
      r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (k+1 : ℝ))
  have hh : HasSum (fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1))
      (r^(k+1)*(r/(1-r)^2+(k+1)/(1-r))) := by
    have h2 := hs.mul_left (r^(k+1))
    have e1 : (fun b : ℕ => r^(k+1) * ((b : ℝ) * r^b + ((k : ℝ)+1) * r^b)) =
        fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1) := by
      ext n
      have : r^(n+k+1) = r^(k+1)*r^n := by
        rw [show n+k+1 = n+(k+1) by omega, pow_add]; ring
      rw [this]; ring
    have e2 : r^(k+1) * (r/(1-r)^2 + ((k:ℝ)+1) * (1-r)⁻¹) =
        r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by simp only [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  rw [← hh.tsum_eq]
  apply Summable.tsum_le_tsum _ _ hh.summable
  · intro n
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast a_le_index (j := n+k+1) (by omega))
      (pow_nonneg hr0 _)
  · simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (f := fun n : ℕ => a (n+1)*r^(n+1)) k).2
        (summable_renewal hr0 hr1)

lemma renewalSeries_thirteen_twentyfifths_lt_one : renewalSeries (13/25) < 1 := by
  have hs := (summable_renewal (r := (13/25 : ℝ)) (by norm_num) (by norm_num)).sum_add_tsum_nat_add 8
  have ht := renewal_tail_majorant (r := (13/25 : ℝ)) (by norm_num) (by norm_num) 8
  change (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) + _ = renewalSeries (13/25) at hs
  have hfinite : (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) < 9/10 := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9,
      log_seven_bounds.2]
  have htail : (∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1)) < 1/10 := by
    exact ht.trans_lt (by norm_num)
  have heq : (∑' n : ℕ, a (n+1+8)*(13/25 : ℝ)^(n+1+8)) =
      ∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1) := by
    congr 1
  simp only [heq] at hs
  linarith

lemma renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one :
    1 < renewalSeries (137/250) := by
  have hs := summable_renewal (r := (137/250 : ℝ)) (by norm_num) (by norm_num)
  have hl := hs.sum_le_tsum (Finset.range 8)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (137/250) at hl
  have hfinite : 1 < (∑ n ∈ Finset.range 8, a (n+1)*(137/250 : ℝ)^(n+1)) := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9,
      log_seven_bounds.1]
  exact hfinite.trans_le hl

lemma collision_rho_bounds : (13/25 : ℝ) < rho ∧ rho < 137/250 := by
  constructor
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩)
      (show (13/25 : ℝ) ∈ Set.Ico 0 1 by norm_num) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_thirteen_twentyfifths_lt_one]
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show (137/250 : ℝ) ∈ Set.Ico 0 1 by norm_num)
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one]

lemma collision_lambda_bounds : (3/5 : ℝ) < lam ∧ lam < 2/3 := by
  have he3 : Real.exp (3/5 : ℝ) < 250/137 := by
    have he : (Real.exp (3/5 : ℝ))^5 < (250/137 : ℝ)^5 := by
      calc
        _ = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
        _ < (2.7182818286 : ℝ)^3 := pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
        _ < _ := by norm_num
    exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 5 ≠ 0)).mp he
  have he2 : (25/13 : ℝ) < Real.exp (2/3 : ℝ) := by
    have he : (25/13 : ℝ)^3 < (Real.exp (2/3 : ℝ))^3 := by
      calc
        _ < (2.7182818283 : ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 3 ≠ 0)).mp he
  unfold lam
  constructor
  · apply (Real.lt_log_iff_exp_lt (div_pos zero_lt_one rho_pos)).mpr
    apply he3.trans
    apply (lt_div_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.2]
  · apply (Real.log_lt_iff_lt_exp (div_pos zero_lt_one rho_pos)).mpr
    apply lt_trans _ he2
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeMassSplit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split a finite prime family at an arbitrary coordinate without multiplying
by the number of possible prefixes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_parts_injective {N n : ℕ} (hn : n ≤ N) :
    Function.Injective (fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)) := by
  intro p q he
  funext j
  by_cases hj : j.val < n
  · exact congrFun (congrArg Prod.fst he) ⟨j.val,hj⟩
  · have hh := congrFun (congrArg Prod.snd he) ⟨j.val-n,by have := j.isLt; omega⟩
    simpa only [primeFinal,Nat.add_sub_of_le (Nat.le_of_not_gt hj)] using hh

lemma reciprocalShiftWeight_split {N n : ℕ} (hn : n ≤ N) (p : Fin N → ℕ) :
    reciprocalShiftWeight p = reciprocalShiftWeight (primeInitial p n hn)*
      reciprocalShiftWeight (primeFinal p n) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  have ht : (∏ j : Fin (n+d-n), (p ⟨n+j.val,by have := j.isLt; omega⟩-1)) =
      ∏ j : Fin d, (p (Fin.natAdd n j)-1) :=
    by
      have he := Fin.prod_congr' (a := n+d-n) (b := d)
        (fun j : Fin d => p (Fin.natAdd n j)-1) (by omega)
      simpa only [Fin.natAdd,Fin.val_cast] using he
  unfold primeInitial primeFinal reciprocalShiftWeight
  rw [ht,Fin.prod_univ_add,Nat.cast_mul,mul_inv]
  rfl

lemma prime_pi_mass {N : ℕ} (T : Fin N → Finset ℕ) :
    (∑ p ∈ Fintype.piFinset T, reciprocalShiftWeight p) =
      ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [reciprocalShiftWeight,Nat.cast_prod,Finset.prod_inv_distrib]

/-- Each suffix coordinate can have its own arithmetic restriction. The prefix
is counted once, with its original reciprocal mass. -/
theorem prime_mass_split {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (T : Fin (N-n) → Finset ℕ)
    (hT : ∀ p ∈ Q, ∀ j, primeFinal p n j ∈ T j) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
        ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  classical
  let F := fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)
  have he : (∑ p ∈ Q, reciprocalShiftWeight p) =
      ∑ z ∈ Q.image F, reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun p _ q _ he => prime_parts_injective hn he)]
    exact Finset.sum_congr rfl (fun p _ => reciprocalShiftWeight_split hn p)
  rw [he]
  have hsub : Q.image F ⊆ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Fintype.mem_piFinset.mpr (hT p hp)⟩
  calc
    _ ≤ ∑ z ∈ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T,
        reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (reciprocalShiftWeight_nonneg _) (reciprocalShiftWeight_nonneg _))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul,prime_pi_mass]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeReciprocalBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short reciprocal-prime bound needed for the unrestricted suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma shifted_prime_reciprocal_le_log {p : ℕ} (hp : p.Prime) :
    ((p-1 : ℕ) : ℝ)⁻¹ ≤ 2*Real.log ((p : ℝ)/(p-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  rw [hc]
  have ht0 : (0 : ℝ) < (p : ℝ)/(p-1) := div_pos hp0 hs
  have ht1 : (1 : ℝ) ≤ (p : ℝ)/(p-1) := (le_div_iff₀ hs).mpr (by linarith)
  have ht2 : (p : ℝ)/(p-1) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos ht0
  have hnon := Real.log_nonneg ht1
  have he : ((p-1 : ℝ))⁻¹=((p : ℝ)/(p-1))*(1-((p : ℝ)/(p-1))⁻¹) := by
    field_simp
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hlog ht0.le).trans
    (mul_le_mul_of_nonneg_right ht2 hnon)

lemma prime_reciprocal_mass_log_product (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ 2*Real.log (primeEulerProduct N) := by
  have he : (Nat.primesLE N)=(Finset.Icc 2 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
  rw [primeEulerProduct,Real.log_prod (by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2.two_le
    have hh' : (2 : ℝ) ≤ p := by exact_mod_cast hh
    exact (div_pos (by linarith) (by linarith)).ne'),Finset.mul_sum,← he]
  exact Finset.sum_le_sum (fun p hp => shifted_prime_reciprocal_le_log (Nat.mem_primesLE.mp hp).2)

theorem prime_reciprocal_mass_bound (hmertens : MertensProductInput) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → 0 ≤ B N →
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(1+B N) := by
  obtain ⟨C,hC,hprod⟩ := hmertens
  refine ⟨2*(1+|Real.log C|),by positivity,?_⟩
  intro N hN hB
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpos : 0 < primeEulerProduct N := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hh := Real.log_le_log hpos (hprod N hN)
  rw [Real.log_mul hC.ne' hlog.ne'] at hh
  calc
    _ ≤ 2*Real.log (primeEulerProduct N) := prime_reciprocal_mass_log_product N
    _ ≤ 2*(Real.log C+B N) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by nlinarith [le_abs_self (Real.log C),abs_nonneg (Real.log C)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDiscardCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common dyadic endpoint for the short suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma discardExponent_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ discardExponent b ∧ Real.log (discardExponent b : ℝ) ≤ 2*b+1 := by
  have he := Real.add_one_le_exp (2*b)
  have hm := Nat.le_ceil (Real.exp (2*b))
  have hm0 : (2 : ℝ) ≤ discardExponent b := by dsimp [discardExponent] <;> linarith
  refine ⟨by exact_mod_cast hm0,?_⟩
  have hc : (discardExponent b : ℝ) ≤ 2*Real.exp (2*b) := by
    have hu := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (2*b) from (Real.exp_pos _).le)
    dsimp [discardExponent]
    linarith
  calc
    _ ≤ Real.log (2*Real.exp (2*b)) := Real.log_le_log (by linarith) hc
    _ = Real.log 2+2*b := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]

lemma discardPrimeBound_bounds {b : ℝ} (hb : 2 ≤ b) :
    4 ≤ discardPrimeBound b ∧ 0 ≤ B (discardPrimeBound b) ∧
    B (discardPrimeBound b) ≤ 2*b+1 ∧
    Real.exp (Real.exp ((6/5 : ℝ)*b)) ≤ discardPrimeBound b := by
  obtain ⟨hM,hlogM⟩ := discardExponent_bounds hb
  have hM2 : (2 : ℝ) ≤ discardExponent b := by exact_mod_cast hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hlog2low : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hB : B (discardPrimeBound b)=Real.log ((discardExponent b : ℝ)*Real.log 2) := by
    simp only [discardPrimeBound,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  refine ⟨?_,?_,?_,?_⟩
  · have he := Nat.pow_le_pow_right (by norm_num : 0<2) hM
    exact he
  · rw [hB]
    apply Real.log_nonneg
    nlinarith
  · rw [hB]
    have hh : (discardExponent b : ℝ)*Real.log 2 ≤ discardExponent b := by nlinarith
    exact (Real.log_le_log (by positivity) hh).trans hlogM
  · have he : (2 : ℝ) ≤ Real.exp ((4/5 : ℝ)*b) := by
      linarith [Real.add_one_le_exp ((4/5 : ℝ)*b)]
    have hsplit : Real.exp (2*b)=Real.exp ((6/5 : ℝ)*b)*Real.exp ((4/5 : ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hceil := Nat.le_ceil (Real.exp (2*b))
    change Real.exp (2*b) ≤ (discardExponent b : ℝ) at hceil
    have hh : Real.exp ((6/5 : ℝ)*b) ≤ (discardExponent b : ℝ)*Real.log 2 := by
      rw [hsplit] at hceil
      nlinarith [Real.exp_pos ((6/5 : ℝ)*b)]
    have hNpos : (0 : ℝ) < discardPrimeBound b := by
      unfold discardPrimeBound
      positivity
    apply (Real.le_log_iff_exp_le hNpos).mp
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExceptionalPrimeLayer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A restricted coordinate in a late layer costs its own reciprocal mass;
the initial segment retains the projected simplex saving. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prime_mass_one_exception {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (j : Fin (N-n)) (U V : Finset ℕ)
    (hU : ∀ p ∈ Q, ∀ k, primeFinal p n k ∈ U)
    (hV : ∀ p ∈ Q, primeFinal p n j ∈ V) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
  classical
  have hh := prime_mass_split hn Q (fun k => if k=j then V else U) (by
    intro p hp k
    split_ifs with hk
    · subst k; exact hV p hp
    · exact hU p hp k)
  have he : (∏ k : Fin (N-n), ∑ q ∈ (if k=j then V else U), ((q-1 : ℕ) : ℝ)⁻¹) =
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true, if_true]
    congr 1
    calc
      _ = ∏ _k ∈ (Finset.univ.erase j), ∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [ite_eq_right (Finset.mem_erase.mp hk).1]
      _ = _ := by simp
  rw [he] at hh
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalInternalDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum every non-head normality failure, retaining all basic witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonnegative_sum_biUnion_le {α β : Type*} (I : Finset α) (S : α → Finset β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ I.biUnion S, f b) ≤ ∑ a ∈ I, ∑ b ∈ S a, f b := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁ := S a) (s₂ := I.biUnion S) (f := f)
    have hn : 0 ≤ ∑ b ∈ S a ∩ I.biUnion S, f b := Finset.sum_nonneg (fun b _ => hf b)
    linarith

lemma reverse_geometric_sum {M H : ℕ} (hH : H ≤ M) :
    (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) ≤ polynomialGeometricTail 0 rho H := by
  let T := (Finset.Icc 0 (M-H)).image (fun i => M-i-H)
  have hi : Set.InjOn (fun i => M-i-H) (↑(Finset.Icc 0 (M-H)) : Set ℕ) := by
    intro i hi j hj he
    have h1 := Finset.mem_Icc.mp hi
    have h2 := Finset.mem_Icc.mp hj
    change M-i-H=M-j-H at he
    omega
  have he : (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) = ∑ n ∈ T, rho^(H+n) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have := Finset.mem_Icc.mp hi
    omega
  rw [he]
  have hs : Summable (fun n : ℕ => rho^(H+n)) :=
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).comp_injective
      (by intro n m hh; omega)
  simpa only [polynomialGeometricTail,pow_zero,one_mul] using
    hs.sum_le_tsum T (fun n _ => (pow_pos rho_pos _).le)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateNormalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normality prime-mass saving at the full-fiber construction's cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma candidate_total_prime_mass : ∃ D : ℝ,0 < D ∧ ∀ b : ℝ,2 ≤ b →
    (∑ p ∈ Nat.primesLE (discardPrimeBound b),((p-1:ℕ):ℝ)⁻¹) ≤ D*(2*b+2) := by
  obtain ⟨D,hD,hbound⟩ := prime_reciprocal_mass_bound mertensProductInput
  refine ⟨D,hD,?_⟩
  intro b hb
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  apply (hbound _ (by omega) hBN).trans
  exact mul_le_mul_of_nonneg_left (by linarith only [hBU]) hD.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordDimensionScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary lower bounds for the dimension and volume normalization. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma dimension_exponential_lower : ∀ᶠ x : ℝ in atTop,
    Real.exp ((3/5:ℝ)*(m x:ℝ)) ≤ B x := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with x hθ hB
  have hbpos : 0 < B x := (Real.exp_pos 1).trans_le hB
  have hlogB : 1 ≤ Real.log (B x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  have hloglog : 0 ≤ Real.log (Real.log (B x)) := Real.log_nonneg hlogB
  have hm : (m x:ℝ) ≤ psi (B x) := by
    have hh := hθ.1
    change 0 ≤ psi (B x)-(m x:ℝ) at hh
    linarith only [hh]
  have hm' := (le_div_iff₀ lam_pos).mp hm
  have hLam := mul_le_mul_of_nonneg_right collision_lambda_bounds.1.le
    (Nat.cast_nonneg (m x) : (0:ℝ) ≤ m x)
  have he : (3/5:ℝ)*(m x:ℝ) ≤ Real.log (B x) := by
    change (m x:ℝ)*lam ≤ Real.log (B x)-Real.log (Real.log (B x)) at hm'
    nlinarith only [hm',hLam,hloglog]
  simpa only [Real.exp_log hbpos] using Real.exp_le_exp.mpr he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixCoordinates
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinates of the triangular prefix simplex in its slack variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSlack_shift (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) (k : ℕ) :
    prefixSlack (N-i) (fun j => u (i+j)) k = prefixSlack N u (i+k) := by
  have hs : (∑ j ∈ Finset.range (N+1),
      if i+k < j then a (j-(i+k))*u j else 0) =
      ∑ j ∈ Finset.range (N-i+1), if k < j then a (j-k)*u (i+j) else 0 := by
    rw [show N+1 = i+(N-i+1) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range i,
        if i+k < j then a (j-(i+k))*u j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.add_lt_add_iff_left, Nat.add_sub_add_left]
  simp only [prefixSlack, hs]

lemma prefix_coordinate_slacks (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    u i = ∑ k ∈ Finset.range (N-i+1), g k*prefixSlack N u (i+k) := by
  have hh := weighted_slack_identity (N-i) (fun j => u (i+j))
  simp only [prefixSlack_shift N u hi, Nat.add_zero] at hh
  exact hh.symm

lemma prefix_coordinate_full_sum (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i < N) :
    u (i+1) = ∑ j ∈ Finset.range N,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0 := by
  rw [prefix_coordinate_slacks N u (by omega : i+1 ≤ N)]
  have hsplit := Finset.sum_range_add
    (fun j => if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) i (N-i)
  rw [Nat.add_sub_of_le hi.le] at hsplit
  rw [hsplit]
  have hz : (∑ j ∈ Finset.range i,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  have he : N-(i+1)+1 = N-i := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.le_add_right, ite_true, if_true, Nat.add_sub_cancel_left]
  congr 2
  omega

/-- The inverse of the determinant-one triangular slack map. -/
theorem prefixLinear_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*prefixLinear N u j else 0 := by
  have hh := prefix_coordinate_full_sum N (extendPrefix N u) i.isLt
  have hv : extendPrefix N u (i.val+1) = u i := by simp [extendPrefix]
  rw [hv] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [← prefixLinear_vector, prefixVector_extend]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictContractionCost
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube row contraction has a bounded full Jacobian. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma rowContractionError_nonneg (h : ℕ) : 0 ≤ rowContractionError h := by
  unfold rowContractionError
  positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictPrefixContraction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal contraction imposes strict Ford rows while preserving prime order. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixRegion_coordinate_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (i : Fin N) : 0 ≤ u i := by
  rw [prefixLinear_coordinate N u i]
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (g_pos _).le (hu.1 j)
  · exact le_rfl

lemma contractedPrefix_subset_prefixRegion {N : ℕ} {B : ℝ} {β : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) : contractedPrefix N B β ⊆ prefixRegion N B 0 0 := by
  intro v hv
  refine ⟨?_,by simpa only [sub_zero] using hv.2.2.2⟩
  intro i
  have hh := (hv.2.2.1 i).trans (div_le_self (hv.1 i) (hβ i))
  rw [prefixLinear_apply]
  change 0 ≤ v i-_
  linarith only [hh]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit-coordinate errors preserve strict rows when paid from their margin. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma strict_row_cube {N : ℕ} (u v : Fin N → ℝ) (i : Fin N) {r e : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0) ≤ r*u i)
    (hdist : ∀ j,|u j-v j| ≤ 1)
    (hmargin : ((N-i.val:ℕ):ℝ)^2+1 ≤ e*v i) :
    (∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ (r+e)*v i := by
  have hd := (le_abs_self _).trans (prefixLinear_cube_error u v hdist i)
  have hvu := (neg_le_abs _).trans (hdist i)
  have hweight : (1-r)*(v i-u i) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hvu (by linarith only [hr1] : 0 ≤ 1-r)
    nlinarith only [hh,hr]
  rw [prefixLinear_apply,prefixLinear_apply] at hd
  nlinarith only [hd,hrow,hweight,hmargin]

lemma strict_gap_cube {N : ℕ} (u v : Fin N → ℝ) (i j : Fin N) {r e : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hgap : u j ≤ r*u i)
    (hdist : ∀ k,|u k-v k| ≤ 1) (hmargin : 2 ≤ e*v i) :
    v j ≤ (r+e)*v i := by
  have hi := (le_abs_self _).trans (hdist i)
  have hj := (neg_le_abs _).trans (hdist j)
  have hmul := mul_le_mul_of_nonneg_left hi hr
  nlinarith only [hgap,hi,hj,hmul,hr1,hmargin]

lemma strict_top_cube {N : ℕ} (u v : Fin N → ℝ) {B₀ B : ℝ}
    (hrow : (∑ j : Fin N,a (j.val+1)*u j) ≤ B₀)
    (hdist : ∀ j,|u j-v j| ≤ 1) (hmargin : B₀+(N:ℝ)^2 ≤ B) :
    (∑ j : Fin N,a (j.val+1)*v j) ≤ B := by
  have hh := (neg_le_abs _).trans (prefixBudget_cube_error u v hdist)
  linarith only [hrow,hh,hmargin]

lemma reciprocal_row_margin {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    e/6 ≤ (1+e/2)⁻¹-(1+e)⁻¹ := by
  have h₁ : 0 < 1+e/2 := by positivity
  have h₂ : 0 < 1+e := by positivity
  have hid : (1+e/2)⁻¹-(1+e)⁻¹=e/(2*(1+e/2)*(1+e)) := by field_simp <;> ring
  rw [hid]
  apply (le_div_iff₀ (by positivity : 0 < 2*(1+e/2)*(1+e))).mpr
  have hprod : 2*(1+e/2)*(1+e) ≤ 6 := by nlinarith only [he.le,he1]
  nlinarith only [mul_le_mul_of_nonneg_left hprod he.le]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_InverseCubeMargin
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial threshold pays for each inverse-cube row margin. -/
noncomputable section
namespace TotientAsymptotic

lemma inverse_cube_margin {h : ℕ} (hh : 1 ≤ h) {u v : ℝ}
    (hu : 100*(h:ℝ)^5 ≤ u) (hdist : |u-v| ≤ 1) :
    0 < v ∧ (h:ℝ)^2+1 ≤
      ((1+1/(10*(h:ℝ)^3))⁻¹-(1+1/(5*(h:ℝ)^3))⁻¹)*v := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := lt_of_lt_of_le zero_lt_one hh'
  have hp3 : 1 ≤ (h:ℝ)^3 := one_le_pow₀ hh'
  have hp5 : 1 ≤ (h:ℝ)^5 := one_le_pow₀ hh'
  have h35 : (h:ℝ)^3 ≤ (h:ℝ)^5 := pow_le_pow_right₀ hh' (by omega)
  have hd := (le_abs_self _).trans hdist
  have hv : 0 < v := by nlinarith only [hu,hd,hp5]
  refine ⟨hv,?_⟩
  have hbase : 30*(h:ℝ)^5+30*(h:ℝ)^3 ≤ v := by
    nlinarith only [hu,hd,hp5,h35]
  have hquot : (h:ℝ)^2+1 ≤ v/(30*(h:ℝ)^3) := by
    apply (le_div_iff₀ (by positivity : 0 < 30*(h:ℝ)^3)).mpr
    convert hbase using 1 <;> first | rfl | ring
  have he : 0 < 1/(5*(h:ℝ)^3) := by positivity
  have he1 : 1/(5*(h:ℝ)^3) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 5*(h:ℝ)^3)).mpr
    linarith only [hp3]
  have hmargin := reciprocal_row_margin he he1
  have heq : 1/(5*(h:ℝ)^3)/2=1/(10*(h:ℝ)^3) := by ring
  rw [heq] at hmargin
  apply hquot.trans
  have hh := mul_le_mul_of_nonneg_right hmargin hv.le
  convert hh using 1 <;> first | rfl | ring

lemma inverse_cube_top_margin {m n : ℕ} (hn : n ≤ m) {B : ℝ}
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    B/(1+1/(5*(m+1:ℝ)^3))+(n:ℝ)^2 ≤ B/(1+1/(10*(m+1:ℝ)^3)) := by
  have he := (inverse_cube_margin (h:=m+1) (by omega)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hB) (by simp : |B-B| ≤ 1)).2
  have hn' : (n:ℝ) ≤ m+1 := by exact_mod_cast (show n ≤ m+1 by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg n) hn' 2
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hid : ((1+1/(10*(m+1:ℝ)^3))⁻¹-(1+1/(5*(m+1:ℝ)^3))⁻¹)*B=
      B/(1+1/(10*(m+1:ℝ)^3))-B/(1+1/(5*(m+1:ℝ)^3)) := by ring
  rw [hid] at he
  linarith only [he,hs]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive-volume family retains half of every margin in its unit grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma geometric_family_unit_cube {m n : ℕ} {B c : ℝ} (hn : n ≤ m)
    {u v : Fin n → ℝ} (hu : u ∈ geometricContractedFamily m n B c)
    (hdist : ∀ i,|u i-v i| ≤ 1)
    (hlarge : ∀ i,100*((m-i.val:ℕ):ℝ)^5 ≤ u i)
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    v ∈ relaxedGeometricFamily m n B (c/2) := by
  have hi (i : Fin n) : 1 ≤ m-i.val := by have := i.isLt; omega
  have herr (i : Fin n) : rowContractionError (m-(i.val+1)) =
      1/(5*((m-i.val:ℕ):ℝ)^3) := by
    unfold rowContractionError
    have he : m-(i.val+1)+1=m-i.val := by have := i.isLt; omega
    have he' : ((m-(i.val+1):ℕ):ℝ)+1=((m-i.val:ℕ):ℝ) := by
      exact_mod_cast he
    rw [he']
  have hhalf (i : Fin n) : rowContractionError (m-(i.val+1))/2 =
      1/(10*((m-i.val:ℕ):ℝ)^3) := by rw [herr]; ring
  have hmargin (i : Fin n) := inverse_cube_margin (hi i) (hlarge i) (hdist i)
  have hpos (i : Fin n) : 0 < v i := (hmargin i).1
  have hgap (i j : Fin n) (hij : i < j) :
      v j ≤ v i/(1+rowContractionError (m-(i.val+1))/2) := by
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have he : 2 ≤ e*v i := by
      have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^2 :=
        one_le_pow₀ (by exact_mod_cast hi i)
      have hh := (hmargin i).2
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hp,hh]
    have hg := strict_gap_cube u v i j hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.2.2 i j hij) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hg
  refine ⟨⟨fun i => (hpos i).le,?_,?_,?_⟩,?_,hgap⟩
  · intro i j hij
    apply (hgap i j hij).trans_lt
    apply div_lt_self (hpos i)
    have he : 0 < rowContractionError (m-(i.val+1)) := by
      unfold rowContractionError
      positivity
    linarith
  · intro i
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have hh := (hmargin i).2
    have hni : ((n-i.val:ℕ):ℝ) ≤ ((m-i.val:ℕ):ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (n-i.val)) hni 2
    have he : ((n-i.val:ℕ):ℝ)^2+1 ≤ e*v i := by
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hs,hh]
    have hrw := strict_row_cube u v i hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.1.2.2.1 i) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hrw
  · apply strict_top_cube u v hu.1.2.2.2 hdist
    have he : 1/(5*(m+1:ℝ)^3)/2=1/(10*(m+1:ℝ)^3) := by
      field_simp
      ring
    simpa only [rowContractionError,he] using inverse_cube_top_margin hn hB
  · intro i
    have hh := (le_abs_self _).trans (hdist i)
    have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^5 := one_le_pow₀ (by exact_mod_cast hi i)
    have hcu := hu.2.1 i
    have hlu := hlarge i
    nlinarith only [hh,hp,hcu,hlu]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricLowerBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two numerical margins needed for the inner prime grid. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma geometric_dominates_polynomial {c : ℝ} (hc : 0 < c) (A : ℝ) (k : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ h : ℕ,H ≤ h → A*(h:ℝ)^k ≤ c*(rho^h)⁻¹ := by
  have hlim : Tendsto (fun h : ℕ => A*((h:ℝ)^k*rho^h)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one k rho_pos.le rho_lt_one).const_mul A
  have ht := hlim.eventually (eventually_lt_nhds hc)
  obtain ⟨H,hH⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop H] with J hJ
  intro h hh
  have hs := (hH h (hJ.trans hh)).le
  apply (le_div_iff₀ (pow_pos rho_pos h)).mpr
  simpa only [div_eq_mul_inv,mul_assoc] using hs

lemma ambient_polynomial_budget (A : ℝ) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,A*(m x:ℝ)^k ≤ B x := by
  have ht : Tendsto (fun x : ℝ => A*(m x:ℝ)^k*
      Real.exp (-((3/5:ℝ)*(m x:ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (k:ℝ) (3/5) (by norm_num : (0:ℝ) < 3/5)).comp
        (tendsto_natCast_atTop_atTop.comp m_tendsto)
    simpa only [Real.rpow_natCast,mul_zero,Function.comp_apply,neg_mul,mul_assoc] using h.const_mul A
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    dimension_exponential_lower] with x hx hB
  have hs : A*(m x:ℝ)^k ≤ Real.exp ((3/5:ℝ)*(m x:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos ((3/5:ℝ)*(m x:ℝ))).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at hh
    exact hh
  exact hs.trans hB

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGridLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass in grids with a large reverse linear lower envelope. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

lemma sum_exp_neg_linear_prefix_sharp {N : ℕ} {c : ℝ} (hc : 0 < c)
    (b : Fin N → ℕ) (hb : ∀ i,c*(N-i.val:ℕ) ≤ (b i:ℝ)) :
    (∑ i,Real.exp (-(b i:ℝ))) ≤ Real.exp (-c)/(1-Real.exp (-c)) := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin N,q^(N-i.val) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [←Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by nlinarith only [hb i])
    _ = ∑ j ∈ Finset.range N,q^(j+1) := by
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
        congr 1
        have := i.isLt
        omega
    _ = q*(∑ j ∈ Finset.range N,q^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ,mul_comm]
    _ ≤ q*(∑' j : ℕ,q^j) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)) hq0
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1]; rfl

theorem grid_prime_mass_lower : ∃ c₀ : ℝ,0 < c₀ ∧
    ∀ {N : ℕ} (K : Finset (Fin N → ℕ)),
      (∀ b ∈ K,∀ i,1 ≤ b i ∧ c₀*(N-i.val:ℕ) ≤ (b i:ℝ)) →
      (K.card:ℝ)/2 ≤ gridPrimeMass K := by
  obtain ⟨C,hC,hgrid⟩ := grid_prime_mass_error_of_sum fordUnitPrimeBoxInput
  let c₀ := Real.log (1+4*C)
  have hc : 0 < c₀ := Real.log_pos (by linarith)
  have hq : Real.exp (-c₀)=1/(1+4*C) := by
    rw [Real.exp_neg,Real.exp_log (by linarith : 0 < 1+4*C)]
    exact (one_div _).symm
  have hbudget : C*(Real.exp (-c₀)/(1-Real.exp (-c₀)))=1/4 := by
    rw [hq]
    field_simp [hC.ne']
    ring
  have hexp : Real.exp (C*(Real.exp (-c₀)/(1-Real.exp (-c₀))))-1 ≤ 1/2 := by
    rw [hbudget]
    have he := Real.exp_bound_div_one_sub_of_interval (x:=1/4) (by norm_num) (by norm_num)
    norm_num at he
    linarith only [he]
  refine ⟨c₀,hc,?_⟩
  intro N K hK
  have he := hgrid K (Real.exp (-c₀)/(1-Real.exp (-c₀)))
    (fun b hb i => (hK b hb i).1)
    (fun b hb => sum_exp_neg_linear_prefix_sharp hc b (fun i => (hK b hb i).2))
  have hlo := (abs_le.mp he).1
  have hh := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg K.card)
  linarith only [hlo,hh]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixBoxGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite prime grids covering concrete bounded prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma prefixRegion_coordinate_upper {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (i : Fin N) : u i ≤ B/a (i.val+1) := by
  apply (le_div_iff₀ (a_pos (by omega))).mpr
  have hh : a (i.val+1)*u i ≤ ∑ j : Fin N,a (j.val+1)*u j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (a_pos (j:=j.val+1) (by omega)).le
      (prefixRegion_coordinate_nonneg hu j)) (Finset.mem_univ i)
  have hb := hh.trans (by simpa only [sub_zero] using hu.2)
  simpa only [mul_comm] using hb

lemma prefixBoxGrid_covers (N : ℕ) (B : ℝ) :
    prefixRegion N B 0 0 ⊆ gridRegion (prefixBoxGrid N B) := by
  intro u hu
  let b : Fin N → ℕ := fun i => ⌊u i⌋₊+1
  have hgrid : b ∈ prefixBoxGrid N B := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    exact ⟨by dsimp [b]; omega,
      Nat.add_le_add_right (Nat.floor_mono (prefixRegion_coordinate_upper hu i)) 1⟩
  have hcell : u ∈ unitGridCell b := by
    intro i _
    dsimp [b]
    rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    exact ⟨Nat.floor_le (prefixRegion_coordinate_nonneg hu i),Nat.lt_floor_add_one _⟩
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hgrid,hcell⟩⟩

lemma prefixBoxGrid_positive {N : ℕ} {B : ℝ} {b : Fin N → ℕ}
    (hb : b ∈ prefixBoxGrid N B) (i : Fin N) : 1 ≤ b i :=
  (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb i)).1

lemma prefix_outer_grid_covers {N : ℕ} {B : ℝ} {S : Set (Fin N → ℝ)}
    (hS : S ⊆ prefixRegion N B 0 0) :
    S ⊆ gridRegion (gridOuter (prefixBoxGrid N B) S) := by
  intro u hu
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp (prefixBoxGrid_covers N B (hS hu))
  obtain ⟨hb,hcell⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨hb,u,hcell,hu⟩,hcell⟩⟩

theorem positive_prefix_grid_mass : ∃ c : ℝ,0 < c ∧
    ∀ {N : ℕ} (B : ℝ) (S : Set (Fin N → ℝ)),
      S ⊆ prefixRegion N B 0 0 →
      (∀ u ∈ S,∀ i,c*(N-i.val:ℕ) ≤ u i) →
      volume.real S/2 ≤ gridPrimeMass (gridOuter (prefixBoxGrid N B) S) := by
  obtain ⟨c,hc,hprime⟩ := grid_prime_mass_lower
  refine ⟨c,hc,?_⟩
  intro N B S hS hlower
  let K := gridOuter (prefixBoxGrid N B) S
  have hK : ∀ b ∈ K,∀ i,1 ≤ b i ∧ c*(N-i.val:ℕ) ≤ (b i:ℝ) := by
    intro b hb i
    obtain ⟨hb,u,hcell,hu⟩ := Finset.mem_filter.mp hb
    exact ⟨prefixBoxGrid_positive hb i,(hlower u hu i).trans
      (hcell i (Set.mem_univ _)).2.le⟩
  have hcard : volume.real S ≤ (K.card:ℝ) := by
    have hh := measureReal_mono (prefix_outer_grid_covers hS)
      (by rw [volume_gridRegion]; exact ENNReal.natCast_ne_top _)
    simpa only [Measure.real,gridRegion_volume_real] using hh
  exact (div_le_div_of_nonneg_right hcard (by norm_num : (0:ℝ) ≤ 2)).trans (hprime K hK)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricPrimeRegion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer grid has both positive prime mass and strict arithmetic coordinates. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ambient_successor_fifth_budget :
    ∀ᶠ x : ℝ in atTop,100*(m x+1:ℝ)^5 ≤ B x := by
  filter_upwards [ambient_polynomial_budget 3200 5,
    m_tendsto.eventually (eventually_ge_atTop 1)] with x hx hm
  have hm' : (1:ℝ) ≤ m x := by exact_mod_cast hm
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ m x+1)
    (show (m x:ℝ)+1 ≤ 2*m x by linarith only [hm']) 5
  have he : (2*(m x:ℝ))^5=32*(m x:ℝ)^5 := by ring
  rw [he] at hpow
  linarith only [hpow,hx]

lemma geometric_grid_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ b ∈ geometricPrimeGrid x c n,
        ∀ v : Fin n → ℝ,v ∈ unitGridCell b →
          v ∈ relaxedGeometricFamily (m x) n (B x) (c/2) := by
  filter_upwards [geometric_dominates_polynomial hc 100 5] with H hH
  filter_upwards [ambient_successor_fifth_budget] with x hx
  intro n hn b hb v hv
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  apply geometric_family_unit_cube (by omega) hfamily
    (unitGridCell_coordinate_distance hu hv) _ hx
  intro i
  exact (hH _ (by have := i.isLt; omega)).trans (hfamily.2.1 i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadLimitedPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with the leading tail separated from the new head. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma headLimitedPrimeGrid_subset {x c : ℝ} {n : ℕ} :
    headLimitedPrimeGrid x c n ⊆ geometricPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

lemma head_limited_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        ∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x := by
  filter_upwards [geometric_grid_coordinates hc] with H hH
  filter_upwards [hH,B_tendsto.eventually (eventually_ge_atTop (100:ℝ))] with x hx hB
  intro n hn p hp
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hp,hcell⟩ := mem_primeBoxTuples_iff.mp hpb
  refine ⟨hp,hx n hn b (headLimitedPrimeGrid_subset hb) _ hcell,?_⟩
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  have hdist := unitGridCell_coordinate_distance hu hcell
  intro i
  have hi := (neg_le_abs _).trans (hdist i)
  have hu := hfamily.2 i
  nlinarith only [hi,hu,hB]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NaturalCoordinateUpper
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coordinate scale at each fixed distance below the natural dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma direct_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    B x*rho^(m x)/(m x:ℝ)=alpha (theta x)*bandCenterRatio x := by
  have hh := inverse_scale_eq hB hm
  have hi := congrArg (fun z : ℝ => z⁻¹) hh
  simpa only [inv_div,inv_inv] using hi

lemma natural_coordinate_scale_upper : ∃ A : ℝ,0 < A ∧
    ∀ H : ℕ,∀ᶠ x : ℝ in atTop,
      0 < m x-H ∧ B x*rho^(m x)/((m x-H:ℕ):ℝ) ≤ A := by
  refine ⟨4*lam/rho,div_pos (mul_pos (by norm_num) lam_pos) rho_pos,?_⟩
  intro H
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    m_tendsto.eventually (eventually_gt_atTop (2*H)),
    bandCenterRatio_tendsto.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2)),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with x hphase hB hm hc hc0
  have hm0 : 0 < m x := by omega
  have hn : 0 < m x-H := by omega
  refine ⟨hn,?_⟩
  have hbasic : B x*rho^(m x)/(m x:ℝ) ≤ 2*lam/rho := by
    rw [direct_scale_eq hB hm0]
    have hh := mul_le_mul (alpha_le _ hphase) hc.le hc0.le
      (div_pos lam_pos rho_pos).le
    exact hh.trans_eq (by ring)
  have hsize : (m x:ℝ) ≤ 2*((m x-H:ℕ):ℝ) := by
    exact_mod_cast (show m x ≤ 2*(m x-H) by omega)
  have hnm : (0:ℝ) < ((m x-H:ℕ):ℝ) := by exact_mod_cast hn
  have hbasic' := (div_le_iff₀ (show (0:ℝ) < (m x:ℝ) by exact_mod_cast hm0)).mp hbasic
  apply (div_le_iff₀ hnm).mpr
  have hmul := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*lam/rho from (div_pos (mul_pos (by norm_num) lam_pos) rho_pos).le)
  exact hbasic'.trans (hmul.trans_eq (by ring))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCoordinateBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turning buffered concentration into geometric upper bounds at every index. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localCoordinateCap_geometric {n m : ℕ} {B A : ℝ} (hn : 0 < n)
    (hnm : n ≤ m) (hA : 0 < A) (hscale : B*rho^m/(n:ℝ) ≤ A)
    (hB : 0 ≤ B) (i : Fin n) :
    localCoordinateCap n B i ≤ 2*A*(m-i.val:ℕ)*(rho^(m-i.val))⁻¹ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : rho^(i.val+1)*rho^(m-i.val)=rho^m*rho := by
    rw [←pow_add,show i.val+1+(m-i.val)=m+1 by have := i.isLt; omega,pow_succ]
  have he : localCoordinateCap n B i*rho^(m-i.val) =
      2*(B*rho^m/(n:ℝ))*rho*(n-i.val:ℕ) := by
    unfold localCoordinateCap
    calc
      _ = (2*B*(n-i.val:ℕ)/(n:ℝ))*(rho^(i.val+1)*rho^(m-i.val)) := by ring
      _ = _ := by rw [hpow]; ring
  have hdim : ((n-i.val:ℕ):ℝ) ≤ (m-i.val:ℕ) := by
    exact_mod_cast Nat.sub_le_sub_right hnm i.val
  have hs0 : 0 ≤ B*rho^m/(n:ℝ) := div_nonneg (mul_nonneg hB (pow_pos rho_pos _).le) hn'.le
  have hr : (B*rho^m/(n:ℝ))*rho ≤ A :=
    (mul_le_of_le_one_right hs0 rho_lt_one.le).trans hscale
  have hb : 2*((B*rho^m/(n:ℝ))*rho)*(n-i.val:ℕ) ≤
      2*A*(m-i.val:ℕ) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hdim
    · exact Nat.cast_nonneg _
    · positivity
  change localCoordinateCap n B i ≤ (2*A*(m-i.val:ℕ))/rho^(m-i.val)
  apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
  rw [he]
  nlinarith only [hb]

lemma locally_concentrated_all_coordinates {m n L : ℕ} {B c A : ℝ}
    (hL : L+2 ≤ n) (hnm : n ≤ m) (hB : 0 ≤ B) (hA : 0 < A)
    (hscale : B*rho^m/(n:ℝ) ≤ A)
    {u : Fin n → ℝ} (hu : u ∈ locallyConcentratedFamily m n B c L) :
    ∀ i : Fin n,u i ≤
      2*A*(m-i.val+L+2:ℕ)*(rho^(m-i.val+L+2))⁻¹ := by
  intro i
  let j : Fin n := ⟨min i.val (n-(L+2)),by omega⟩
  have hji : j ≤ i := by show j.val ≤ i.val; exact min_le_left _ _
  have hjL : j.val+L+2 ≤ n := by
    have hh : j.val ≤ n-(L+2) := min_le_right _ _
    omega
  have horder : u i ≤ u j := hu.1.1.1.2.1.antitone hji
  have hcap := hu.2 j hjL
  have hgeo := localCoordinateCap_geometric (by omega) hnm hA hscale hB j
  have hdist : m-j.val ≤ m-i.val+L+2 := by
    dsimp [j]
    have := i.isLt
    omega
  have hd := index_inv_pow_mono hdist
  exact horder.trans (hcap.trans (hgeo.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*A by positivity))))

theorem local_candidate_coordinate_envelope : ∃ A : ℝ,0 < A ∧
    ∀ H L : ℕ,∀ᶠ x : ℝ in atTop,∀ c : ℝ,
      ∀ u ∈ locallyConcentratedFamily (m x) (m x-H) (B x) c L,
        ∀ i : Fin (m x-H),u i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹ := by
  obtain ⟨A,hA,hscale⟩ := natural_coordinate_scale_upper
  refine ⟨2*A,by positivity,?_⟩
  intro H L
  filter_upwards [hscale H,m_tendsto.eventually (eventually_ge_atTop (H+L+2)),
    B_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with x hx hm hB
  intro c u hu i
  exact locally_concentrated_all_coordinates (by omega) (Nat.sub_le _ _) hB hA hx.2 hu i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed normality: a polynomial logarithmic cutoff beats each bounded local tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localNormalityScale_factor (h : ℕ) :
    (Real.log (localNormalityScale h))^(-1/6:ℝ)=Real.exp (-(h:ℝ)^4/6) := by
  rw [localNormalityScale,Real.log_exp,←Real.exp_mul]
  congr 1
  ring

/-- The two index choices and every local tuple coordinate are included
in this bound. The cutoff U may grow exponentially with the tail length. -/
theorem local_normality_geometric_decay {C D A : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ U : ℝ,1 ≤ U → Real.log (6*U) ≤ A*h →
      ∀ n : ℕ,n ≤ h →
        (h:ℝ)^2*(C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*(D*(2*U+2))^n ≤ rho^h := by
  let M := |Real.log C|+|Real.log D|+lam+8*A+10
  have hM : 10 ≤ M := by dsimp [M] <;> linarith [lam_pos,abs_nonneg (Real.log C),abs_nonneg (Real.log D)]
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (6*M))] with h hh
  intro U hU hlog n hn
  have hh1 : (1:ℝ) ≤ h := by nlinarith only [hM,hh]
  have hh0 : (0:ℝ) < h := zero_lt_one.trans_le hh1
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hbase : 0 < 2*U+2 := by linarith only [hU]
  have hlogbase : Real.log (2*U+2) ≤ A*h :=
    (Real.log_le_log hbase (by linarith only [hU] : 2*U+2 ≤ 6*U)).trans hlog
  have hlogh : Real.log (h:ℝ) ≤ h := Real.log_le_self hh0.le
  have hnR : (n:ℝ) ≤ h := by exact_mod_cast hn
  have hnt : (n:ℝ)*(Real.log D+Real.log (2*U+2)) ≤
      (h:ℝ)*(|Real.log D|+A*h) :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnR (by positivity))
  have hh2 : (h:ℝ) ≤ (h:ℝ)^2 := by nlinarith only [hh1]
  have hsmall : |Real.log C|+(2+6*A+|Real.log D|+lam)*(h:ℝ)+A*(h:ℝ)^2 ≤ M*(h:ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (h:ℝ)^2 by nlinarith only [hh1])
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+6*A+|Real.log D|+lam by
        linarith only [hA,abs_nonneg (Real.log D),lam_pos])
    dsimp [M]
    nlinarith only [hc,hd,hA,sq_nonneg (h:ℝ)]
  have hlarge : 6*M ≤ (h:ℝ)^2 := by nlinarith only [hh,hh1]
  have hextra := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hlarge)
  have hexponent : 2*Real.log (h:ℝ)+Real.log C+6*Real.log (2*U+2)+
      (n:ℝ)*(Real.log D+Real.log (2*U+2))-(h:ℝ)^4/6 ≤ -lam*h := by
    nlinarith only [hlogh,hlogbase,hnt,hsmall,hextra,le_abs_self (Real.log C)]
  have heq : (h:ℝ)^2*(C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*(D*(2*U+2))^n =
      Real.exp (2*Real.log (h:ℝ)+Real.log C+6*Real.log (2*U+2)+
        (n:ℝ)*(Real.log D+Real.log (2*U+2))-(h:ℝ)^4/6) := by
    have htwo : Real.exp (2*Real.log (h:ℝ))=(h:ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h:ℝ)) 2
    have hsix : Real.exp (6*Real.log (2*U+2))=(2*U+2)^6 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hbase] using Real.exp_nat_mul (Real.log (2*U+2)) 6
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,hsix,
      Real.exp_nat_mul,Real.exp_log hC,Real.exp_add,Real.exp_log hD,Real.exp_log hbase]
    rw [show -(h:ℝ)^4/6= -((h:ℝ)^4/6) by ring,Real.exp_neg]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h:ℝ)=(h:ℝ)*Real.log rho by rw [hlogrho]; ring,
    Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's proved exceptional-prime estimate at each local indexed scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma localNormalityScale_gt_two (h : ℕ) : 2 < localNormalityScale h := by
  have he := Real.one_le_exp (show 0 ≤ (h:ℝ)^4 by positivity)
  have htwo : 2 < Real.exp 1 := by
    linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
  exact htwo.trans_le (Real.exp_le_exp.mpr he)

theorem local_non_normal_prime_mass : ∃ C : ℝ,0 < C ∧ ∀ h : ℕ,∀ b : ℝ,2 ≤ b →
    (∑ p ∈ nonNormalPrimes (localNormalityScale h) (discardPrimeBound b),
      ((p-1:ℕ):ℝ)⁻¹) ≤ C*(2*b+2)^6*Real.exp (-(h:ℝ)^4/6) := by
  obtain ⟨C,hC,hbound⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨C,hC,?_⟩
  intro h b hb
  have hs : 0 ≤ (h:ℝ)^4 := by positivity
  have hS := localNormalityScale_gt_two h
  have hBS : 0 ≤ B (localNormalityScale h) := by
    simpa only [localNormalityScale,B,Real.log_exp] using hs
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  have hM := discardExponent_bounds hb
  have he := hbound _ hS hBS _ hN
  rw [show Nat.clog 2 (discardPrimeBound b)=discardExponent b from
    Nat.clog_pow 2 _ (by norm_num)] at he
  rw [localNormalityScale_factor] at he
  have hBpow : (B ((2:ℝ)^discardExponent b))^5 ≤ (2*b+2)^5 := by
    apply pow_le_pow_left₀
    · simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBN
    · exact (show B ((2:ℝ)^discardExponent b) ≤ 2*b+1 by
        simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBU).trans
          (by linarith)
  calc
    _ ≤ C*(B ((2:ℝ)^discardExponent b))^5*(1+Real.log (discardExponent b))*
        Real.exp (-(h:ℝ)^4/6) := he
    _ ≤ C*(2*b+2)^5*(2*b+2)*Real.exp (-(h:ℝ)^4/6) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul (mul_le_mul_of_nonneg_left hBpow hC.le) (by linarith only [hM.2])
      · have hm2 : (1:ℝ) ≤ discardExponent b := by
          exact_mod_cast (show 1 ≤ discardExponent b by omega)
        linarith only [Real.log_nonneg hm2]
      · positivity
    _ = _ := by ring


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with geometric upper bounds at every local index. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma localPrimeGrid_subset {x c : ℝ} {L n : ℕ} :
    localPrimeGrid x c L n ⊆ headLimitedPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

theorem local_prime_mass_lower_base : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ gridPrimeMass (localPrimeGrid x c L (N+2)) := by
  obtain ⟨c,δ,L,hc,hδ,hL,hvolume⟩ := locally_concentrated_volume_lower
  obtain ⟨c₀,hc₀,hprime⟩ := positive_prefix_grid_mass
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  filter_upwards [geometric_dominates_polynomial hc c₀ 1,eventually_ge_atTop 1]
    with H hH hH1
  filter_upwards [hvolume H hH1] with x hx
  intro N hN
  have hn : N+2 ≤ m x := by omega
  let S := locallyConcentratedFamily (m x) (N+2) (B x) c L
  have hS : S ⊆ prefixRegion (N+2) (B x/(1+rowContractionError (m x))) 0 0 := by
    intro u hu
    exact contractedPrefix_subset_prefixRegion
      (fun i => by linarith only [rowContractionError_nonneg (m x-(i.val+1))]) hu.1.1.1
  have hlinear (u) (hu : u ∈ S) (i : Fin (N+2)) : c₀*(N+2-i.val:ℕ) ≤ u i := by
    have hdist : H ≤ m x-i.val := by have := i.isLt; omega
    have hdim : ((N+2-i.val:ℕ):ℝ) ≤ (m x-i.val:ℕ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    calc
      _ ≤ c₀*(m x-i.val:ℕ) := mul_le_mul_of_nonneg_left hdim hc₀.le
      _ ≤ c*(rho^(m x-i.val))⁻¹ := by simpa only [pow_one] using hH _ hdist
      _ ≤ u i := hu.1.1.2.1 i
  have hmass := hprime (B x/(1+rowContractionError (m x))) S hS hlinear
  calc
    _ = (δ*G x (N+2))/2 := by ring
    _ ≤ volume.real S/2 := div_le_div_of_nonneg_right (hx N hN) (by norm_num)
    _ ≤ _ := hmass

theorem local_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) ∧
        ∀ i,primePrefixCoord p i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹+1 := by
  obtain ⟨A,hA,hupper⟩ := local_candidate_coordinate_envelope
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [head_limited_prime_coordinates hc] with H hH
  filter_upwards [hH,hupper H L] with x hx hu
  intro n hn p hp
  have hpn : p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n) := by
    obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hpb⟩
  obtain ⟨hpr,hr,hcap⟩ := hx n hn p hpn
  refine ⟨hpr,hr,hcap,?_⟩
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨_,u,hucell,hfamily⟩ := Finset.mem_filter.mp hb
  have hpcell := (mem_primeBoxTuples_iff.mp hpb).2
  have hdist := unitGridCell_coordinate_distance hucell hpcell
  have hdim : n=m x-H := by omega
  subst n
  intro i
  have hupp := hu c u hfamily i
  have hclose := (neg_le_abs _).trans (hdist i)
  linarith only [hupp,hclose]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeSupport
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each suffix lies in a prime interval determined only by its distance from the end. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma localPrimeHeight_ge_two {A : ℝ} (hA : 0 ≤ A) (L h : ℕ) :
    2 ≤ localPrimeHeight A L h := by
  unfold localPrimeHeight
  have hn : 0 ≤ A*(h+L+2:ℕ)*(rho^(h+L+2))⁻¹ :=
    mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (inv_pos.mpr (pow_pos rho_pos _)).le
  linarith only [hn]

lemma localPrimeHeight_mono {A : ℝ} (hA : 0 ≤ A) (L : ℕ) :
    Monotone (localPrimeHeight A L) := by
  intro h k hhk
  have hh : h+L+2 ≤ k+L+2 := by omega
  have he := mul_le_mul_of_nonneg_left (index_inv_pow_mono hh) hA
  unfold localPrimeHeight
  simpa only [mul_assoc,add_comm] using add_le_add_right he 2

lemma prime_mem_discard_bound_of_coordinate {p : ℕ} (hp : p.Prime)
    {U : ℝ} (hU : 2 ≤ U) (hcoord : B p ≤ U) :
    p ∈ Nat.primesLE (discardPrimeBound U) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have he : (p:ℝ) ≤ Real.exp (Real.exp U) :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hp1)).mp hcoord)
  have hupper := (discardPrimeBound_bounds hU).2.2.2
  have hUU : U ≤ (6/5:ℝ)*U := by linarith only [hU]
  have hh : (p:ℝ) ≤ discardPrimeBound U :=
    he.trans ((Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hUU)).trans hupper)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hh,hp⟩

theorem local_prime_suffix_support {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
        ∀ i j : Fin n,i ≤ j →
          p j ∈ Nat.primesLE (discardPrimeBound (localPrimeHeight A L (m x-i.val))) := by
  obtain ⟨A,hA,hdata⟩ := local_prime_coordinates hc
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hdata L] with H hH
  filter_upwards [hH] with x hx
  intro n hn p hp i j hij
  obtain ⟨hprime,_,_,hupper⟩ := hx n hn p hp
  have hji : m x-j.val ≤ m x-i.val := Nat.sub_le_sub_left hij _
  have hcoord : B (p j) ≤ localPrimeHeight A L (m x-i.val) := by
    apply le_trans (hupper j)
    have hm := localPrimeHeight_mono hA.le L hji
    unfold localPrimeHeight at hm ⊢
    linarith only [hm]
  exact prime_mem_discard_bound_of_coordinate (hprime j) (localPrimeHeight_ge_two hA.le _ _) hcoord

lemma localPrimeHeight_log_bound {A : ℝ} (hA : 0 < A) (L : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ᶠ h : ℕ in atTop,
      Real.log (6*localPrimeHeight A L h) ≤ D*h := by
  let D := |Real.log (6*(A+2))|+2*(1+lam)
  have hD : 0 < D := by dsimp [D] <;> linarith [lam_pos,abs_nonneg (Real.log (6*(A+2)))]
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop (L+2),eventually_ge_atTop 1] with h hh hh1
  let k := h+L+2
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by dsimp [k]; omega)
  have hk0 : (0:ℝ) < k := zero_lt_one.trans_le hk1
  have hkh : (k:ℝ) ≤ 2*h := by exact_mod_cast (show k ≤ 2*h by dsimp [k]; omega)
  have hr : (1:ℝ) ≤ (rho^k)⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hkr : (1:ℝ) ≤ (k:ℝ)*(rho^k)⁻¹ := one_le_mul_of_one_le_of_one_le hk1 hr
  have hu : localPrimeHeight A L h ≤ (A+2)*(k:ℝ)*(rho^k)⁻¹ := by
    unfold localPrimeHeight
    change A*(k:ℝ)*(rho^k)⁻¹+2 ≤ _
    nlinarith only [hkr]
  have hu0 : 0 < localPrimeHeight A L h :=
    lt_of_lt_of_le (by norm_num) (localPrimeHeight_ge_two hA.le L h)
  have hlog := Real.log_le_log (mul_pos (by norm_num) hu0)
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 6))
  have he : 6*((A+2)*(k:ℝ)*(rho^k)⁻¹) = (6*(A+2))*(k:ℝ)*(rho^k)⁻¹ := by ring
  rw [he,Real.log_mul (mul_pos (by linarith) hk0).ne' (inv_ne_zero (pow_pos rho_pos _).ne'),
    Real.log_mul (by linarith : 6*(A+2) ≠ 0) hk0.ne',Real.log_inv,Real.log_pow] at hlog
  have hlrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [hlrho] at hlog
  have hklog := Real.log_le_self hk0.le
  have hconst := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ h by exact_mod_cast hh1)
    (abs_nonneg (Real.log (6*(A+2))))
  have hlinear := mul_le_mul_of_nonneg_left hkh (show 0 ≤ 1+lam by linarith [lam_pos])
  dsimp [D]
  nlinarith only [hlog,hklog,hconst,hlinear,le_abs_self (Real.log (6*(A+2)))]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityLayer
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-index normality exclusion in the local candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem local_normality_layer_mass {c : ℝ} (hc : 0 < c) :
    ∃ A C D : ℝ,0 < A ∧ 0 < C ∧ 0 < D ∧
    ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ i j : Fin (m x-H),i ≤ j →
      let h := m x-i.val
      let U := localPrimeHeight A L h
      (∑ p ∈ localAbnormalTuples x c L H i j,reciprocalShiftWeight p) ≤
        C*G x (m x-H)*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6)*
          (D*(2*U+2))^(m x-H-i.val-1) := by
  obtain ⟨A,hA,hsupport⟩ := local_prime_suffix_support hc
  obtain ⟨C₀,hC₀,hprefix⟩ := geometric_initial_mass_le_base (half_pos hc)
  obtain ⟨E,hE,hexcept⟩ := local_non_normal_prime_mass
  obtain ⟨D,hD,htotal⟩ := candidate_total_prime_mass
  refine ⟨A,C₀*E,D,hA,mul_pos hC₀ hE,hD,?_⟩
  intro L
  filter_upwards [hsupport L,hprefix,head_limited_prime_coordinates hc] with H hH hpref hcoords
  filter_upwards [hH,hpref,hcoords,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hsup hpre hco hm hB
  intro i j hij
  dsimp only
  let N := m x-H
  let h := m x-i.val
  let U := localPrimeHeight A L h
  let Q := localAbnormalTuples x c L H i j
  have hU : 2 ≤ U := localPrimeHeight_ge_two hA.le L h
  have hi : i.val ≤ N := Nat.le_of_lt i.isLt
  let k : Fin (N-i.val) := ⟨j.val-i.val,by have := j.isLt; omega⟩
  have hmem (p) (hp : p ∈ Q) : p ∈ gridPrimeTuples (localPrimeGrid x c L N) :=
    (Finset.mem_filter.mp hp).1
  have hheadmem (p) (hp : p ∈ Q) : p ∈ gridPrimeTuples (headLimitedPrimeGrid x c N) := by
    obtain ⟨b,hb,hp⟩ := Finset.mem_biUnion.mp (hmem p hp)
    exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hp⟩
  have hq (p) (hp : p ∈ Q) : (∀ l,(p l).Prime) ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) (c/2) := by
    have hh := hco N (Nat.sub_add_cancel hm) p (hheadmem p hp)
    exact ⟨hh.1,hh.2.1⟩
  have hsp (p) (hp : p ∈ Q) (l : Fin (N-i.val)) :
      primeFinal p i.val l ∈ Nat.primesLE (discardPrimeBound U) := by
    apply hsup N (Nat.sub_add_cancel hm) p (hmem p hp) i
      ⟨i.val+l.val,by have := l.isLt; omega⟩
    show i.val ≤ i.val+l.val
    omega
  have hbad (p) (hp : p ∈ Q) :
      primeFinal p i.val k ∈ nonNormalPrimes (localNormalityScale h) (discardPrimeBound U) := by
    apply Finset.mem_filter.mpr
    refine ⟨hsp p hp k,?_⟩
    have he : primeFinal p i.val k=p j := by
      apply congrArg p
      apply Fin.ext
      change i.val+(j.val-i.val)=j.val
      omega
    rw [he]
    exact (Finset.mem_filter.mp hp).2
  have hmass := prime_mass_one_exception hi Q k _ _ hsp hbad
  have hpm := hpre N i.val (Nat.sub_add_cancel hm) hi Q hq
  have hem := hexcept h U hU
  have htm := htotal U hU
  have hright : (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      (C₀*G x N)*(E*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*
        (D*(2*U+2))^(N-i.val-1) := by
    apply hmass.trans
    apply mul_le_mul
    · exact mul_le_mul hpm hem (Finset.sum_nonneg (fun _ _ => by positivity))
        (mul_nonneg hC₀.le (G_pos hB _).le)
    · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) htm _
    · positivity
    · exact mul_nonneg (mul_nonneg hC₀.le (G_pos hB _).le) (by positivity)
  convert hright using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of all local normality failures in the actual candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem local_normality_discard {c : ℝ} (hc : 0 < c) :
    ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∑ p ∈ localNormalityFailures x c L H,reciprocalShiftWeight p) ≤
        polynomialGeometricTail 0 rho H*G x (m x-H) := by
  classical
  obtain ⟨A,C,D,hA,hC,hD,hlayer⟩ := local_normality_layer_mass hc
  intro L
  obtain ⟨J,hJ,hheight⟩ := localPrimeHeight_log_bound hA L
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hheight.and (local_normality_geometric_decay hC hD hJ.le))
  filter_upwards [hlayer L,eventually_ge_atTop K,eventually_ge_atTop 1] with H hH hHK hH1
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  let N := m x-H
  have hsum_i (i : Fin N) :
      (∑ p ∈ (Finset.univ.filter (fun j => i ≤ j)).biUnion (localAbnormalTuples x c L H i),
        reciprocalShiftWeight p) ≤ G x (m x-H)*rho^(m x-i.val) := by
    let h := m x-i.val
    let U := localPrimeHeight A L h
    let E := C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6)*(D*(2*U+2))^(N-i.val-1)
    have hHi : H ≤ h := by have := i.isLt; dsimp [N,h] at *; omega
    have hh1 : (1:ℝ) ≤ h := by exact_mod_cast (hH1.trans hHi)
    have hU : 2 ≤ U := localPrimeHeight_ge_two hA.le L h
    have hh0 : 0 ≤ E := by dsimp [E] <;> positivity
    have hkernel : (h:ℝ)^2*E ≤ rho^h := by
      have hh := (hK h (hHK.trans hHi)).2 U
        (le_trans (by norm_num) (localPrimeHeight_ge_two hA.le L h))
        ((hK h (hHK.trans hHi)).1) (N-i.val-1) (by dsimp [N,h]; omega)
      simpa only [E,mul_assoc] using hh
    have hcard : ((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ) ≤ (h:ℝ)^2 := by
      have hcN : (Finset.univ.filter (fun j : Fin N => i ≤ j)).card ≤ N-i.val := by
        rw [show Finset.univ.filter (fun j : Fin N => i ≤ j)=Finset.Ici i by ext j; simp]
        simp
      have hh : ((N-i.val:ℕ):ℝ) ≤ h := by exact_mod_cast (show N-i.val ≤ h by dsimp [N,h]; omega)
      have hcR : ((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ) ≤ ((N-i.val:ℕ):ℝ) := by exact_mod_cast hcN
      nlinarith only [hcR,hh,hh1]
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),
          ∑ p ∈ localAbnormalTuples x c L H i j,reciprocalShiftWeight p :=
        by
          convert nonnegative_sum_biUnion_le _ _ _ reciprocalShiftWeight_nonneg using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          ext p
          simp
      _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),G x (m x-H)*E := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := hx i j (Finset.mem_filter.mp hj).2
        dsimp only at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [E,U,h,N]
        ring
      _ = G x (m x-H)*(((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ)*E) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ G x (m x-H)*((h:ℝ)^2*E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hh0) (G_pos hB _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (G_pos hB _).le
  have hgeo : (∑ i : Fin N,rho^(m x-i.val)) ≤ polynomialGeometricTail 0 rho H := by
    change (∑ i : Fin N,(fun j : ℕ => rho^(m x-j)) i.val) ≤ _
    have he := Fin.sum_univ_eq_sum_range (fun j => rho^(m x-j)) N
    rw [he]
    apply le_trans _ (reverse_geometric_sum hm)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,by have := Finset.mem_range.mp hi; dsimp [N] at this; omega⟩
    · intro i _ _
      exact (pow_pos rho_pos _).le
  calc
    _ ≤ ∑ i : Fin N,∑ p ∈ (Finset.univ.filter (fun j => i ≤ j)).biUnion
        (localAbnormalTuples x c L H i),reciprocalShiftWeight p :=
      by
        convert nonnegative_sum_biUnion_le _ _ _ reciprocalShiftWeight_nonneg using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ext p
        simp [localNormalityFailures,N]
    _ ≤ ∑ i : Fin N,G x (m x-H)*rho^(m x-i.val) := Finset.sum_le_sum (fun i _ => hsum_i i)
    _ = G x (m x-H)*(∑ i : Fin N,rho^(m x-i.val)) := (Finset.mul_sum _ _ _).symm
    _ ≤ G x (m x-H)*polynomialGeometricTail 0 rho H := mul_le_mul_of_nonneg_left hgeo (G_pos hB _).le
    _ = _ := mul_comm _ _

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalRegularPrimeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive prime mass satisfying every needed indexed normality condition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem local_regular_prime_mass_oai : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      δ*G x (m x-H) ≤ ∑ p ∈ localRegularPrimeTuples x c L H,reciprocalShiftWeight p := by
  classical
  obtain ⟨c,δ,L,hc,hδ,hL,hmass⟩ := local_prime_mass_lower_base
  have ht := polynomialGeometricTail_tendsto 0 rho
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  filter_upwards [hmass,local_normality_discard hc L,
    ht.eventually (eventually_lt_nhds (half_pos hδ))] with H hH hbad htail
  filter_upwards [hH,hbad,m_tendsto.eventually (eventually_ge_atTop (H+2)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hb hm hB
  let N := m x-H
  let Q := gridPrimeTuples (localPrimeGrid x c L N)
  let F := localNormalityFailures x c L H
  have hN : N-2+2+H=m x := by dsimp [N]; omega
  have hmass : δ*G x N ≤ ∑ p ∈ Q,reciprocalShiftWeight p := by
    have hh := hx (N-2) hN
    have he : N-2+2=N := by dsimp [N]; omega
    change δ*G x (N-2+2) ≤ gridPrimeMass (localPrimeGrid x c L (N-2+2)) at hh
    rw [he] at hh
    exact hh
  have hcover : Q ⊆ Q \ F ∪ F := by
    intro p hp
    by_cases hf : p ∈ F
    · exact Finset.mem_union_right _ hf
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,hf⟩)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun p _ _ => reciprocalShiftWeight_nonneg p)
  have hdisj : Disjoint (Q \ F) F := Finset.disjoint_left.mpr
    (fun _ hp hf => (Finset.mem_sdiff.mp hp).2 hf)
  rw [Finset.sum_union hdisj] at hsum
  have hbad' : (∑ p ∈ F,reciprocalShiftWeight p) ≤ (δ/2)*G x N :=
    hb.trans (mul_le_mul_of_nonneg_right htail.le (G_pos hB _).le)
  change (δ/2)*G x N ≤ ∑ p ∈ Q \ F,reciprocalShiftWeight p
  nlinarith only [hmass,hsum,hbad']

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.local_regular_prime_mass_oai := @OAI.TotientAsymptotic.local_regular_prime_mass_oai
