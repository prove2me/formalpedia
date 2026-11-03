-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:37:25.328146+00:00
-- url     : https://prove2.me/submissions/a652b35a-bcff-4504-996e-9a60f748319b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D005
import Definitions.Def_OAIQ093D008

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

/-- A polynomial correction to exponential contraction can be absorbed
uniformly at a time bounded by twice the logarithm of the initial size. -/
theorem exists_logarithmic_contraction_time {C : ℝ} (hC : 0 ≤ C) (b : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ R : ℝ, 0 ≤ R →
      let t := 2 * Real.log (2 + R) + a
      1 ≤ t ∧ C * (1 + t) ^ b * Real.exp (-t) * R ≤ 1 := by
  have hp : Tendsto (fun t : ℝ => t ^ b * Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b : ℝ) (1 / 2) (by norm_num)
  have hs : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [eventually_ge_atTop (z - 1)] with t ht
    linarith
  have heq (t : ℝ) : C * (1 + t) ^ b * Real.exp (-t / 2) =
      (C * Real.exp (1 / 2)) * ((1 + t) ^ b * Real.exp (-(1 / 2) * (1 + t))) := by
    have hh : Real.exp (-t / 2) = Real.exp (1 / 2) * Real.exp (-(1 / 2) * (1 + t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hh]
    ring
  have ht : Tendsto (fun t : ℝ => C * (1 + t) ^ b * Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [heq, Function.comp_def, mul_zero] using
      (hp.comp hs).const_mul (C * Real.exp (1 / 2))
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  let a := max a₀ 1
  refine ⟨a, (by dsimp [a] <;> positivity), fun R hR => ?_⟩
  let t := 2 * Real.log (2 + R) + a
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have ha1 : 1 ≤ a := le_max_right _ _
  have ha : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by dsimp [t] <;> positivity
  have ht1 : 1 ≤ t := by dsimp [t] <;> linarith
  have hta : a₀ ≤ t := (le_max_left _ _).trans (by dsimp [t] <;> linarith)
  have hcoef : C * (1 + t) ^ b * Real.exp (-t / 2) ≤ 1 := (ha₀ t hta).le
  have hsmall : Real.exp (-t / 2) * R ≤ 1 := by
    calc
      Real.exp (-t / 2) * R ≤ Real.exp (-Real.log (2 + R)) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply Real.exp_le_exp.mpr
        dsimp [t]
        linarith
      _ = R / (2 + R) := by rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  refine ⟨ht1, ?_⟩
  have hnonneg : 0 ≤ C * (1 + t) ^ b * Real.exp (-t / 2) := by positivity
  calc
    C * (1 + t) ^ b * Real.exp (-t) * R =
        (C * (1 + t) ^ b * Real.exp (-t / 2)) * (Real.exp (-t / 2) * R) := by
      have hh : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hh]
      ring
    _ ≤ (C * (1 + t) ^ b * Real.exp (-t / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hsmall hnonneg
    _ ≤ 1 := by simpa using hcoef

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

/-- Conjugation costs at most twice the conjugating length. -/
theorem dist_one_conjugate_le (a x : G) :
    dist 1 (a * x * a⁻¹) ≤ 2 * dist 1 a + dist 1 x := by
  have hi : dist 1 a⁻¹ = dist 1 a := by
    simpa only [mul_one, mul_inv_cancel, dist_comm] using (dist_mul_left a 1 a⁻¹).symm
  calc
    dist 1 (a * x * a⁻¹) ≤ dist 1 (a * x) + dist 1 a⁻¹ := dist_one_mul_le _ _
    _ ≤ (dist 1 a + dist 1 x) + dist 1 a⁻¹ := add_le_add (dist_one_mul_le _ _) le_rfl
    _ = _ := by rw [hi]; ring

/-- Exponential contraction up to a polynomial, together with a bounded
unit neighborhood and linear conjugating paths, implies logarithmic distortion. -/
theorem logarithmic_distortion_of_contracting_flow
    {V : Type*} [NormedAddCommGroup V]
    (Exp : V → G) (d : ℝ → G) (T : ℝ → V → V)
    {C L B : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖)
    (hpath : ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t)
    (hlocal : ∀ v, ‖v‖ ≤ 1 → dist 1 (Exp v) ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨a, ha, htime⟩ := exists_logarithmic_contraction_time hC b
  let c := (2 * L * a + B) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ c := by dsimp [c] <;> positivity
  refine ⟨4 * L + c + 1, by positivity, fun v => ?_⟩
  let t := 2 * Real.log (2 + ‖v‖) + a
  obtain ⟨ht1, hsize⟩ := htime ‖v‖ (norm_nonneg v)
  have ht : 0 ≤ t := le_trans zero_le_one ht1
  have hunit : ‖T t v‖ ≤ 1 := (hcontract v t ht).trans hsize
  have hlog : Real.log 2 ≤ Real.log (2 + ‖v‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg v])
  have hconst : 2 * L * a + B ≤ c * Real.log (2 + ‖v‖) := by
    calc
      2 * L * a + B = c * Real.log 2 := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc
  calc
    dist 1 (Exp v) = dist 1 (d t * Exp (T t v) * (d t)⁻¹) := by rw [← hconj v t ht]
    _ ≤ 2 * dist 1 (d t) + dist 1 (Exp (T t v)) := dist_one_conjugate_le _ _
    _ ≤ 2 * (L * t) + B := add_le_add (by gcongr; exact hpath t ht1) (hlocal _ hunit)
    _ = 4 * L * Real.log (2 + ‖v‖) + (2 * L * a + B) := by dsimp [t] <;> ring
    _ ≤ (4 * L + c + 1) * Real.log (2 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast <;> ring

/-- Every continuous one-parameter homomorphism has a linear metric bound
for times at least one, using only boundedness of its compact unit interval. -/
theorem continuous_flow_linear_growth
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num))
    simpa [hd0] using h
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, fun t ht => ?_⟩
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htn : t ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one t).le
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (by linarith : 0 ≤ t)) 1
  have hs : t / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hnr.le, (div_le_one hnr).mpr htn⟩
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have heq : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  calc
    dist 1 (d t) = dist 1 (d (t / n) ^ n) := congrArg (dist 1) heq
    _ ≤ (n : ℝ) * dist 1 (d (t / n)) := dist_one_pow_le _ _
    _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_left hlocal hnr.le
    _ ≤ (2 * C) * t := by nlinarith

/-- For a continuous exponential chart and continuous contracting flow,
polynomially corrected contraction implies an actual logarithmic distance bound.
The compact unit-ball bound and the flow-length bound are derived in the proof. -/
theorem logarithmic_distortion_of_continuous_flow
    {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) (T : ℝ → V → V)
    {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨L, hL, hpath⟩ := continuous_flow_linear_growth d hd hd0 hmul
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) 1).bddAbove_image
    (continuous_const.dist hExp).continuousOn
  have hB0 : 0 ≤ B := (dist_nonneg (x := (1 : G)) (y := Exp 0)).trans
    (hB (mem_image_of_mem _ (by simp : (0 : V) ∈ closedBall 0 1)))
  apply logarithmic_distortion_of_contracting_flow Exp d T hC hL hB0 b hconj hcontract hpath
  intro v hv
  apply hB
  exact mem_image_of_mem _ (by simpa only [mem_closedBall, dist_zero_right] using hv)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The polynomial exponential gives a uniform increment bound on any fixed
bounded set of nilpotent logarithms. -/
theorem norm_exp_sub_one_le_of_pow_eq_zero [NormOneClass A]
    (x : A) {c : ℕ} (hx : x ^ (c + 1) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ‖x‖ ≤ M) :
    ‖NormedSpace.exp x - 1‖ ≤ (c : ℝ) * (1 + M) ^ c := by
  rw [exp_eq_finite_sum_of_pow_eq_zero x hx, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖((k + 1).factorial : ℝ)⁻¹ • x ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + M) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hi : ‖((k + 1).factorial : ℝ)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ = ‖((k + 1).factorial : ℝ)⁻¹‖ * ‖x ^ (k + 1)‖ := norm_smul _ _
        _ ≤ 1 * ‖x ^ (k + 1)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ ≤ (1 + M) ^ (k + 1) := by
          rw [one_mul]
          exact (norm_pow_le _ _).trans
            (pow_le_pow_left₀ (norm_nonneg _) (by linarith) (k + 1))
        _ ≤ (1 + M) ^ c := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hk)
    _ = _ := by simp

end Algebra

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent corrections in a contracting weight flow

The nilpotent part of the infinitesimal action gives a polynomial bound
for its actual analytic exponential. Coupled with scalar exponential
contraction, it gives logarithmic metric distortion of the weight chart.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Split the scalar weight from the nilpotent part in the actual analytic
exponential of the infinitesimal generator. -/
theorem exp_smul_sub_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (N : A) (t : ℝ) :
    NormedSpace.exp (t • (N - 1)) = Real.exp (-t) • NormedSpace.exp (t • N) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute ((-t) • (1 : A)) (t • N) := by
    change ((-t) • (1 : A)) * (t • N) = (t • N) * ((-t) • (1 : A))
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes (-t) (t • N)
  have he : NormedSpace.exp ((-t) • (1 : A)) = Real.exp (-t) • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) (-t)).symm
  rw [show t • (N - 1) = (-t) • (1 : A) + t • N by module,
    NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

/-- The actual exponential of a nilpotent operator has polynomial growth
in its real parameter, with an explicit uniform coefficient. -/
theorem norm_exp_smul_nilpotent_le
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (N : A) {c : ℕ} (hN : N ^ (c + 1) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • N)‖ ≤
      ((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c := by
  have hpow : (t • N) ^ (c + 1) = 0 := by simp [smul_pow, hN]
  have hbound : ‖NormedSpace.exp (t • N) - 1‖ ≤
      (c : ℝ) * (1 + t * ‖N‖) ^ c := by
    apply norm_exp_sub_one_le_of_pow_eq_zero _ hpow (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hbase : 1 + t * ‖N‖ ≤ (1 + ‖N‖) * (1 + t) := by
    nlinarith [norm_nonneg N]
  have hpoly : (1 + t * ‖N‖) ^ c ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase c
  have hone : 1 ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg N]))
      (one_le_pow₀ (by linarith))
  calc
    ‖NormedSpace.exp (t • N)‖ ≤ ‖NormedSpace.exp (t • N) - 1‖ + ‖(1 : A)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (c : ℝ) * (1 + t * ‖N‖) ^ c + 1 := by simpa only [norm_one] using add_le_add hbound le_rfl
    _ ≤ (c : ℝ) * ((1 + ‖N‖) ^ c * (1 + t) ^ c) +
        ((1 + ‖N‖) ^ c * (1 + t) ^ c) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hone
    _ = _ := by ring

/-- The infinitesimal nilpotent correction, with its actual operator
exponential, has exactly the polynomially corrected contraction needed above. -/
theorem norm_contracted_nilpotent_flow_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (v : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-t) • (NormedSpace.exp (t • N)) v‖ ≤
      (((c : ℝ) + 1) * (1 + ‖N‖) ^ c) * (1 + t) ^ c * Real.exp (-t) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * ‖(NormedSpace.exp (t • N)) v‖ ≤
        Real.exp (-t) * (‖NormedSpace.exp (t • N)‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) *
        ((((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c) * ‖v‖) := by
      gcongr
      exact norm_exp_smul_nilpotent_le N hN ht
    _ = _ := by ring

/-- A continuous weight chart with a nilpotent correction in its contracting
action is logarithmically distorted. This is the individual weight-space
estimate, before taking bounded products of generator directions. -/
theorem logarithmic_distortion_of_nilpotent_flow
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp (Real.exp (-t) • (NormedSpace.exp (t • N)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  exact logarithmic_distortion_of_continuous_flow Exp hExp d hd hd0 hmul
    (fun t v => Real.exp (-t) • (NormedSpace.exp (t • N)) v)
    (C := ((c : ℝ) + 1) * (1 + ‖N‖) ^ c) (by positivity) c hconj
    (fun v _ ht => norm_contracted_nilpotent_flow_le N hN v ht)

/-- The same distortion conclusion stated directly for a generator whose
nilpotent part is `N` and whose real weight is `-1`. -/
theorem logarithmic_distortion_of_weight_generator
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • (N - 1))) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  apply logarithmic_distortion_of_nilpotent_flow Exp hExp d hd hd0 hmul N hN
  intro v t ht
  have hh := hconj v t ht
  rw [exp_smul_sub_one N t] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion in Cartan root spaces

Generalized root spaces determine the nilpotent correction to the scalar
weight action. A compatible group conjugation identity then gives logarithmic
distortion.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

attribute [local instance] OAI.PolycyclicRecognition.rootNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.rootNormedSpace
attribute [local instance] OAI.PolycyclicRecognition.rootNontrivial
theorem rootAction_nilpotent_correction (h : H) :
    _root_.IsNilpotent (rootAction H χ h - χ h • 1) := by
  have hn := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, ?_⟩
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hk
  simpa only [map_pow, map_sub, Algebra.algebraMap_eq_smul_one,
    map_smul, map_one, map_zero, rootAction] using hm

/-- Each nonzero real root has a direction where its value is `-1`. -/
theorem exists_contracting_root_direction (hχ : χ.IsNonZero) :
    ∃ h : H, χ h = -1 := by
  have hn : ∃ h : H, χ h ≠ 0 := by
    by_contra! hn
    apply hχ
    exact funext hn
  obtain ⟨h, hh⟩ := hn
  refine ⟨(-(χ h)⁻¹) • h, ?_⟩
  rw [map_smul]
  change -(χ h)⁻¹ * χ h = -1
  rw [neg_mul, inv_mul_cancel₀ hh]

/-- Logarithmic distortion follows for an integrated nonzero root chart.
No semisimplicity or diagonal adjoint action is assumed. -/
theorem root_logarithmic_distortion
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • rootAction H χ h)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  let N := rootAction H χ h + 1
  have hnil : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨k, hk⟩ := hnil
  have hk' : N ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  apply logarithmic_distortion_of_weight_generator Exp hExp d hd hd0 hmul N hk'
  simpa only [N, add_sub_cancel_right] using hconj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

set_option maxHeartbeats 1000000 in
/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

attribute [local instance] OAI.PolycyclicRecognition.instNormedAddCommGroupSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions
attribute [local instance] OAI.PolycyclicRecognition.instNormedSpaceRealSubtypeMemLieSubmoduleLieSubalgebraRootSpaceCoeWeight_solutions
set_option maxHeartbeats 1000000 in
/-- The nilpotence exponent is uniformly bounded by the root-space dimension. -/
theorem rootAction_residual_pow_eq_zero (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ (rootSpace H χ) = 0 := by
  let A : Module.End ℝ (rootSpace H χ) := toEnd ℝ H (rootSpace H χ) h - χ h • 1
  have hn : _root_.IsNilpotent A := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  have hp : A ^ finrank ℝ (rootSpace H χ) = 0 := by
    simpa only [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] using
      A.aeval_self_charpoly
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hp
  simpa only [A, map_pow, map_sub, map_smul, map_one, map_zero, rootAction] using hm

set_option maxHeartbeats 1000000 in
/-- One polynomial controls the residual operator for every Cartan parameter. -/
theorem exists_rootResidual_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : H,
      ‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) := by
  let d := finrank ℝ (rootSpace H χ)
  let b := Module.finBasis ℝ H
  let f := ((rootResidualLinear H χ).comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  let K := ‖f‖
  have hK : 0 ≤ K := norm_nonneg f
  refine ⟨((d : ℝ) + 1) * (1 + K) ^ d * 2 ^ d, by positivity, ?_⟩
  intro h
  have hb : ‖rootAction H χ h - χ h • 1‖ ≤ K * ‖(Module.finBasis ℝ H).equivFun h‖ := by
    have hf : f (b.equivFun h) = rootAction H χ h - χ h • 1 := by
      change rootResidualLinear H χ (b.equivFun.symm (b.equivFun h)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    simpa only [hf] using f.le_opNorm (b.equivFun h)
  have hp : (rootAction H χ h - χ h • 1) ^ (d + 1) = 0 := by
    rw [pow_succ, rootAction_residual_pow_eq_zero, zero_mul]
  have he := norm_exp_smul_nilpotent_le (rootAction H χ h - χ h • 1) hp (t := 1) zero_le_one
  simp only [one_smul, one_add_one_eq_two] at he
  calc
    _ ≤ ((d : ℝ) + 1) * (1 + ‖rootAction H χ h - χ h • 1‖) ^ d * 2 ^ d := he
    _ ≤ ((d : ℝ) + 1) * ((1 + K) * (1 + ‖(Module.finBasis ℝ H).equivFun h‖)) ^ d * 2 ^ d := by
      gcongr
      nlinarith [norm_nonneg (b.equivFun h)]
    _ = _ := by rw [mul_pow]; ring

set_option maxHeartbeats 1000000 in
/-- Restoring the scalar character gives the full root action estimate. -/
theorem exists_rootAction_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : H) (v : rootSpace H χ),
      ‖(NormedSpace.exp (rootAction H χ h)) v‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * Real.exp (χ h) * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_rootResidual_exp_bound H χ
  refine ⟨C, hC, fun h v => ?_⟩
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (χ h) *
        (‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ * ‖v‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (χ h) *
        (C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * ‖v‖) := by
      gcongr
      exact hbound h
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra exponentials as actual group elements

The unit-valued exponential keeps the inverse explicit. This bridges the
operator conjugation identity to a faithful group representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem algebraExpUnit_add_of_commute {x y : A} (hxy : Commute x y) :
    algebraExpUnit (x + y) = algebraExpUnit x * algebraExpUnit y := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hxy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

theorem represented_root_exp_conjugation (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) =
      algebraExpUnit (t • j h) * algebraExpUnit (j v) * (algebraExpUnit (t • j h))⁻¹ := by
  change algebraExpUnit (representedRootVector H χ j
    ((NormedSpace.exp (t • rootAction H χ h)) v)) = _
  rw [represented_root_flow]
  exact algebraExpUnit_conj (algebraExpUnit (t • j h)) (j v)

theorem represented_root_exp_inverse_conjugation
    (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j v) = algebraExpUnit (-(t • j h)) *
      algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) *
        (algebraExpUnit (-(t • j h)))⁻¹ := by
  rw [represented_root_exp_conjugation, algebraExpUnit_neg]
  simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- In an integrated faithful representation, logarithmic root distortion
requires only the exponential matching data. -/
theorem represented_root_logarithmic_distortion
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1) (d : ℝ → G) (hd : Continuous d)
    (hExpρ : ∀ v, ρ (Exp v) = algebraExpUnit (j v))
    (hdρ : ∀ t, ρ (d t) = algebraExpUnit (-(t • j h))) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  have hd0 : d 0 = 1 := by
    apply hρ
    simp only [hdρ, zero_smul, neg_zero, algebraExpUnit_zero, map_one]
  have hmul : ∀ s t, d (s + t) = d s * d t := by
    intro s t
    apply hρ
    rw [map_mul, hdρ, hdρ, hdρ]
    have hc : Commute (-(s • j h)) (-(t • j h)) := by
      exact (((Commute.refl (j h)).smul_left s).smul_right t).neg_left.neg_right
    rw [← algebraExpUnit_add_of_commute hc]
    congr 1
    module
  apply root_logarithmic_distortion H χ Exp hExp h hh d hd hd0 hmul
  intro v t _
  apply hρ
  simp only [map_mul, map_inv, hExpρ, hdρ]
  exact represented_root_exp_inverse_conjugation H χ j h t v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoarseFlowBounds
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse bounds along actual one-parameter subgroups

Continuity and the homomorphism law suffice for the path-mesh estimates.
The additive constant accommodates short parameter intervals without an
extra Riemannian regularity assumption on the ambient metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem continuous_flow_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, dist 1 (d t) ≤ C * (1 + |t|) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).bddAbove_image
    (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have hh := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))
    simpa [hzero] using hh
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨C, hC0, ?_⟩
  intro t
  let n := ⌊|t|⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊|t|⌋₊)
  have htn : |t| ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one |t|).le
  have hnt : (n : ℝ) ≤ |t| + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (abs_nonneg t)) 1
  have hsabs : |t / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr htn
  have hs : t / n ∈ Icc (-1 : ℝ) 1 := abs_le.mp hsabs
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have he : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [he]
  exact (dist_one_pow_le _ _).trans ((mul_le_mul_of_nonneg_left hlocal hn.le).trans
    (by nlinarith))

/-- Differences along the flow have the same uniform bound. -/
theorem continuous_flow_coarse_dist (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, dist (d s) (d t) ≤ C * (1 + |t - s|) := by
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro s t
  have he : d t = d s * d (t - s) := by rw [← hmul]; congr 1; ring
  rw [he]
  have he' : dist (d s) (d s * d (t - s)) = dist 1 (d (t - s)) := by
    simpa only [mul_one] using dist_mul_left (d s) 1 (d (t - s))
  rw [he']
  exact hb _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SupportFlowLegs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual one-parameter legs between support positions

The height along a translated one-parameter leg is the affine segment
between its endpoint heights. Its metric bound is uniform at scale `r`,
with one fixed additive constant for the finite-mesh argument.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [AddCommGroup W] [Module ℝ W]

theorem exists_flowLeg_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G) (r : ℝ), 0 ≤ r → ∀ s t : ℝ,
      dist (flowLeg d x r s) (flowLeg d x r t) ≤ C * r * |t - s| + C := by
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_dist d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro x r hr s t
  rw [flowLeg, flowLeg, dist_mul_left]
  have h := hb (r * s) (r * t)
  rw [← mul_sub, abs_mul, abs_of_nonneg hr] at h
  nlinarith [h]

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
theorem flowLeg_height (π : G →* Multiplicative W) (d : ℝ → G)
    {w₀ w₁ : W} (hd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀))
    {x : G} {r : ℝ} (hx : (π x).toAdd = r • w₀) (t : ℝ) :
    (π (flowLeg d x r t)).toAdd = r • (w₀ + t • (w₁ - w₀)) := by
  rw [flowLeg, map_mul]
  change (π x).toAdd + (π (d (r * t))).toAdd = _
  rw [hx, hd]
  module

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
/-- Convexity keeps every height on the leg inside the scaled template. -/
theorem flowLeg_height_mem (π : G →* Multiplicative W) (d : ℝ → G)
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E)
    (hd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀))
    {x : G} {r : ℝ} (hx : (π x).toAdd = r • w₀) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w ∈ E, (π (flowLeg d x r t)).toAdd = r • w := by
  refine ⟨w₀ + t • (w₁ - w₀), hE.add_smul_sub_mem hw₀ hw₁ ht, ?_⟩
  exact flowLeg_height π d hd hx t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PublishedRootDistortion
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual root distortion from the published linear realization

All contraction, continuity, and conjugation premises of the root-space
distortion theorem are now discharged for the ambient Lie group. Only the
already recorded faithful exponential-realization input remains assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every actual nonzero Cartan root space is logarithmically distorted
in the ambient metric. -/
theorem root_distortion_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : rootSpace H χ,
      dist 1 (Exp v) ≤ D * Real.log (2 + ‖(rootCoordinates H χ) v‖) := by
  let : TopologicalSpace (rootSpace H χ) :=
    (rootNormedAddCommGroup H χ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let d : ℝ → G := fun t => Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  have hEr : Continuous (fun v : rootSpace H χ => Exp v) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (ρ (Exp v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  have hd : Continuous d := by
    apply hind.continuous_iff.mpr
    change Continuous (fun t : ℝ => (ρ (Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) :
      Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch, map_neg, map_smul]
    exact Units.continuous_val.comp (algebraExpUnit_continuous.comp
      (continuous_id.smul continuous_const).neg)
  exact represented_root_logarithmic_distortion H χ j ρ hρ
    (fun v => Exp v) hEr h hh d hd (fun v => hmatch v)
    (fun t => by simp only [d, hmatch, map_neg, map_smul])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DistortedHomomorphisms
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaged homomorphisms vanish on logarithmically distorted flows

A continuous homomorphism is linear on each one-parameter subgroup. A
linear metric bound and logarithmic distortion force that linear value to
vanish. In particular, the stationary mean kills the actual root flows.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter LieAlgebra LieModule
open scoped Topology Manifold

section Flow

variable {G W : Type*} [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The image of a continuous one-parameter subgroup under a continuous
homomorphism is a real-linear one-parameter subgroup. -/
theorem hom_flow_eq_smul
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) (t : ℝ) :
    (l (d t)).toAdd = t • (l (d 1)).toAdd := by
  let a : ℝ →+ W := {
    toFun t := (l (d t)).toAdd
    map_zero' := by rw [hd₀, map_one]; rfl
    map_add' := fun s t => by rw [hdadd, map_mul]; rfl }
  have ha : Continuous a := hl.comp hd
  have h := (a.toRealLinearMap ha).map_smul t (1 : ℝ)
  change a t = t • a 1
  change a (t • (1 : ℝ)) = t • a 1 at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Linear metric control precludes a nonzero homomorphism on a flow of
logarithmic ambient size. -/
theorem hom_eq_one_of_logarithmic_flow
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L D B : ℝ} (hL : 0 ≤ L) (hB : 0 < B)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hdist : ∀ t, dist 1 (d t) ≤ D * Real.log (2 + B * |t|)) :
    ∀ t, l (d t) = 1 := by
  have hscale := hom_flow_eq_smul d hd hd₀ hdadd l hl
  have hat : Tendsto (fun t : ℝ => 2 + B * t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop ((x - 2) / B)] with t ht
    have hh := (div_le_iff₀ hB).mp ht
    nlinarith
  have hden (t : ℝ) : (1 / B) * (2 + B * t) + (-2 / B) = t := by
    field_simp
    ring
  have hlim : Tendsto (fun t : ℝ => L * D * Real.log (2 + B * t) / t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 / B) (-2 / B) 1
      (one_div_ne_zero hB.ne')).comp hat
    change Tendsto (fun t : ℝ => Real.log (2 + B * t) ^ 1 /
      ((1 / B) * (2 + B * t) + (-2 / B))) atTop (𝓝 0) at hh
    simp only [pow_one, hden] at hh
    simpa only [mul_zero, mul_div_assoc] using hh.const_mul (L * D)
  have hle : ∀ᶠ t : ℝ in atTop,
      ‖(l (d 1)).toAdd‖ ≤ L * D * Real.log (2 + B * t) / t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hb := (hbound (d t)).trans (mul_le_mul_of_nonneg_left (hdist t) hL)
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
    apply (le_div_iff₀ ht0).mpr
    nlinarith
  have hz : (l (d 1)).toAdd = 0 := norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto hlim hle) (norm_nonneg _))
  intro t
  change (l (d t)).toAdd = 0
  rw [hscale, hz, smul_zero]

end Flow

variable {G W EG : Type*} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every continuous homomorphism with linear metric control kills the
root exponentials, using their logarithmic distortion. -/
theorem hom_eq_one_on_root_exp
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : LieModule.Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : rootSpace H χ) :
    ∀ t : ℝ, l (Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  obtain ⟨D, hD, hb⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  let B := 1 + ‖rootCoordinates H χ v‖
  have hB : 0 < B := by dsimp [B] <;> positivity
  apply hom_eq_one_of_logarithmic_flow
    (fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun s t => hExp.map_add_smul v s t) l hl hL hB hbound
  intro t
  have h := hb (t • v)
  have hn : 2 + ‖rootCoordinates H χ (t • v)‖ ≤ 2 + B * |t| := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    dsimp [B]
    nlinarith [abs_nonneg t]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) hn) hD.le)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogPolynomialBounds
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic bounds for polynomial corrections -/

noncomputable section

namespace PolycyclicRecognition

/-- A fixed polynomial growth factor contributes at most a fixed multiple
of `log (2 + r)`, including the degree-zero case. -/
theorem log_two_add_polynomial_le {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (b : ℕ) :
    Real.log (2 + A * (1 + r) ^ b) ≤
      ((b : ℝ) + Real.log (2 + A) / Real.log 2) * Real.log (2 + r) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 + r) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hquot : 0 ≤ Real.log (2 + A) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hc : Real.log (2 + A) ≤
      (Real.log (2 + A) / Real.log 2) * Real.log (2 + r) := by
    calc
      _ = (Real.log (2 + A) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hquot
  have hp : 2 + A * (1 + r) ^ b ≤ (2 + A) * (2 + r) ^ b := by
    have hpow : (1 + r) ^ b ≤ (2 + r) ^ b :=
      pow_le_pow_left₀ (by linarith) (by linarith) b
    have hone : 1 ≤ (2 + r) ^ b := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hpow hA]
  calc
    _ ≤ Real.log ((2 + A) * (2 + r) ^ b) := Real.log_le_log (by positivity) hp
    _ = Real.log (2 + A) + (b : ℝ) * Real.log (2 + r) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    _ ≤ _ := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathConcatenation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse metric bounds under path concatenation

The additive error is retained explicitly. This allows logarithmic-diameter
switches and coarse-speed one-parameter legs to use a fixed finite mesh.
-/

namespace PolycyclicRecognition

open scoped unitInterval

variable {X : Type*} [PseudoMetricSpace X] {x y z : X}

theorem PathMetricBound.mono {p : Path x y} {L κ L' κ' : ℝ}
    (h : PathMetricBound p L κ) (hL : L ≤ L') (hκ : κ ≤ κ') :
    PathMetricBound p L' κ' := by
  intro s t
  exact (h s t).trans (add_le_add (mul_le_mul_of_nonneg_right hL (abs_nonneg _)) hκ)

theorem PathMetricBound.symm {p : Path x y} {L κ : ℝ} (h : PathMetricBound p L κ) :
    PathMetricBound p.symm L κ := by
  intro s t
  have hb := h (unitInterval.symm s) (unitInterval.symm t)
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq, sub_sub_sub_cancel_left,
    abs_sub_comm] using hb

theorem PathMetricBound.cast {p : Path x y} {L κ : ℝ} (h : PathMetricBound p L κ)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : PathMetricBound (p.cast hx hy) L κ := h

private theorem pathMetricBound_trans_ordered {p : Path x y} {q : Path y z} {L κ : ℝ}
    (hκ : 0 ≤ κ) (hp : PathMetricBound p L κ) (hq : PathMetricBound q L κ)
    (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    dist ((p.trans q) s) ((p.trans q) t) ≤ (2 * L) * |(s : ℝ) - t| + 2 * κ := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with hs ht ht
  · calc
      _ ≤ L * |2 * (s : ℝ) - 2 * t| + κ := hp _ _
      _ ≤ _ := by
        rw [show 2 * (s : ℝ) - 2 * t = 2 * ((s : ℝ) - t) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
  · calc
      _ ≤ dist (p _) y + dist y (q _) := dist_triangle _ y _
      _ ≤ (L * |2 * (s : ℝ) - 1| + κ) +
          (L * |0 - (2 * (t : ℝ) - 1)| + κ) := by
        apply add_le_add
        · simpa using hp _ 1
        · simpa only [Path.source, Set.Icc.coe_zero] using
            hq 0 ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
              ⟨(not_le.mp ht).le, t.property.2⟩⟩
      _ = _ := by
        rw [abs_of_nonpos (by linarith : 2 * (s : ℝ) - 1 ≤ 0),
          abs_of_nonpos (by linarith : 0 - (2 * (t : ℝ) - 1) ≤ 0),
          abs_of_nonpos (sub_nonpos.mpr hst)]
        ring
  · exfalso
    exact hs (hst.trans ht)
  · calc
      _ ≤ L * |(2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1)| + κ := hq _ _
      _ ≤ _ := by
        rw [show (2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1) =
            2 * ((s : ℝ) - t) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith

/-- Concatenation doubles the common speed and additive error. For a fixed
number of pieces these constants stay independent of the height scale. -/
theorem PathMetricBound.trans {p : Path x y} {q : Path y z} {L κ : ℝ}
    (hκ : 0 ≤ κ) (hp : PathMetricBound p L κ) (hq : PathMetricBound q L κ) :
    PathMetricBound (p.trans q) (2 * L) (2 * κ) := by
  intro s t
  rcases le_total (s : ℝ) t with hst | hts
  · exact pathMetricBound_trans_ordered hκ hp hq s t hst
  · simpa only [dist_comm, abs_sub_comm] using
      pathMetricBound_trans_ordered hκ hp hq t s hts

theorem path_trans_range_mem {S : Set X} {p : Path x y} {q : Path y z}
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : ∀ t, (p.trans q) t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportVisitPaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outward, switch, and return paths

The actual three curves are concatenated, retaining their exact heights and
the logarithmic switch error. This statement is independent of how the
switch estimate is obtained and is used below for the Cartan root curves.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped unitInterval

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [AddCommGroup W] [Module ℝ W]

/-- Concatenate a support leg, a height-zero switch, and the reverse leg.
The constants are uniform over both the translated sheet and the pivot. -/
theorem supportVisitPath_uniform_bound
    (π : G →* Multiplicative W) (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E)
    (hπd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (n d₀ : G),
      π n = 1 → (π d₀).toAdd = r • w₀ →
      ∀ (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1), (∀ t, π (f t) = 1) →
      ∀ (b κ : ℝ), 0 ≤ κ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (n * f (s * b) * (d₀ * d r)) (n * f (t * b) * (d₀ * d r)) ≤ κ) →
      PathMetricBound (supportVisitPath d hd hzero f hf hf₀ n d₀ r b)
        (4 * C * r) (4 * (C + κ)) ∧
        ∀ t, ∃ w ∈ E,
          (π (supportVisitPath d hd hzero f hf hf₀ n d₀ r b t)).toAdd = r • w := by
  obtain ⟨C, hC, hb⟩ := exists_flowLeg_coarse_bound d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro r hr n d₀ hn hd₀ f hf hf₀ hπf b κ hκ hswitch
  let p₀ := flowPath d hd hzero (n * d₀) r
  let p₁ := flowPath d hd hzero (n * f b * d₀) r
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  have hn₀ : (π (n * d₀)).toAdd = r • w₀ := by simpa [hn] using hd₀
  have hn₁ : (π (n * f b * d₀)).toAdd = r • w₀ := by simpa [hn, hπf] using hd₀
  have hp₀ : ∀ t, ∃ w ∈ E, (π (p₀ t)).toAdd = r • w := fun t =>
    flowLeg_height_mem π d hE hw₀ hw₁ hπd hn₀ t.property
  have hp₁ : ∀ t, ∃ w ∈ E, (π (p₁ t)).toAdd = r • w := fun t =>
    flowLeg_height_mem π d hE hw₀ hw₁ hπd hn₁ t.property
  have hq : ∀ t, ∃ w ∈ E, (π (q t)).toAdd = r • w := by
    intro t
    obtain ⟨w, hw, he⟩ := hp₀ 1
    refine ⟨w, hw, ?_⟩
    have he' : π (q t) = π (p₀ 1) := by
      change π (n * f ((t : ℝ) * b) * (d₀ * d r)) = π (flowLeg d (n * d₀) r 1)
      simp [flowLeg, hn, hπf]
    rw [he']
    exact he
  have hp₀b : PathMetricBound p₀ (C * r) (C + κ) := by
    intro s t
    have h := hb (n * d₀) r hr (s : ℝ) (t : ℝ)
    change dist (p₀ s) (p₀ t) ≤ C * r * |(t : ℝ) - s| + C at h
    rw [abs_sub_comm] at h
    linarith
  have hp₁b : PathMetricBound p₁ (C * r) (C + κ) := by
    intro s t
    have h := hb (n * f b * d₀) r hr (s : ℝ) (t : ℝ)
    change dist (p₁ s) (p₁ t) ≤ C * r * |(t : ℝ) - s| + C at h
    rw [abs_sub_comm] at h
    linarith
  have hqb : PathMetricBound q (C * r) (C + κ) := by
    intro s t
    have h := hswitch s s.property t t.property
    change dist (q s) (q t) ≤ κ at h
    have := mul_nonneg (mul_nonneg hC hr) (abs_nonneg ((s : ℝ) - t))
    linarith
  let p := (p₀.trans q).trans p₁.symm
  change PathMetricBound p (4 * C * r) (4 * (C + κ)) ∧
    ∀ t, ∃ w ∈ E, (π (p t)).toAdd = r • w
  constructor
  · have hsum : 0 ≤ C + κ := add_nonneg hC hκ
    have hback : PathMetricBound p₁.symm (2 * (C * r)) (2 * (C + κ)) :=
      hp₁b.symm.mono (by nlinarith [mul_nonneg hC hr]) (by linarith)
    have h := (hp₀b.trans hsum hqb).trans (by positivity) hback
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  · exact path_trans_range_mem (p := p₀.trans q) (q := p₁.symm)
      (S := {g | ∃ w ∈ E, (π g).toAdd = r • w})
      (path_trans_range_mem hp₀ hq) (fun t => hp₁ (unitInterval.symm t))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ParametrizedSupportPaths
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous sampling of prescribed generator words

When the generator indices are fixed and the amplitudes depend continuously
on a parameter, every fixed time sample of the explicitly constructed path
is continuous in that parameter. This retains the measurability needed for
stationary endpoint averaging.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G I : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1)
  (d₀ : G) (r : ℝ)

/-- The explicit word path retains the uniform metric and range bounds of
its actual single-letter visits. -/
theorem supportWordPath_bound
    {W : Type*} [AddCommGroup W] (π : G →* Multiplicative W)
    (P : I → ℝ → Prop) (hπf : ∀ i b, P i b → π (f i b) = 1)
    {S : Set G} (hbase : ∀ n, π n = 1 → n * d₀ ∈ S)
    {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hstep : ∀ n, π n = 1 → ∀ i b, P i b →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b t ∈ S)
    (u : List (I × ℝ)) (hu : ∀ z ∈ u, P z.1 z.2) (n : G) (hn : π n = 1) :
    PathMetricBound (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n)
      (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧
      ∀ t, supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t ∈ S := by
  induction u generalizing n with
  | nil =>
    constructor
    · intro s t
      change dist (n * d₀) (n * d₀) ≤ _
      simp only [dist_self, List.length_nil, pow_zero, mul_one]
      positivity
    · exact fun _ => hbase n hn
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hi := hu (i, b) List.mem_cons_self
    have hu' : ∀ z ∈ u, P z.1 z.2 := fun z hz => hu z (List.mem_cons_of_mem _ hz)
    obtain ⟨hp, hpS⟩ := hstep n hn i b hi
    have hn' : π (n * f i b) = 1 := by rw [map_mul, hn, hπf i b hi, one_mul]
    obtain ⟨hq, hqS⟩ := ih hu' (n * f i b) hn'
    have hpow : 1 ≤ (2 : ℝ) ^ u.length := one_le_pow₀ (by norm_num)
    have hp' := hp.mono
      (show L ≤ L * 2 ^ u.length by nlinarith)
      (show κ ≤ κ * 2 ^ u.length by nlinarith)
    constructor
    · have hb := hp'.trans (mul_nonneg hκ (by positivity)) hq
      have he : n * indexedWordProduct f ((i, b) :: u) * d₀ =
          (n * f i b) * indexedWordProduct f u * d₀ := by
        simp [indexedWordProduct, mul_assoc]
      have hb' := hb.cast rfl he
      convert hb' using 1 <;>
        first | rfl | (simp only [List.length_cons, pow_succ]; ring)
    · exact path_trans_range_mem hpS hqS

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHomKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing on the actual Cartan root factor

Logarithmic distortion kills each root generator under a linearly bounded
continuous homomorphism. The proved generator schemes then kill the whole
constructed nilpotent factor, including every point of its group model.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

include T M hExp realize hl hL hbound

set_option maxHeartbeats 1000000 in
/-- The actual homogeneous letters lie in the kernel. -/
theorem hom_eq_one_on_letter (i : Fin M.letterCount) (t : ℝ) :
    l (Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 :=
  hom_eq_one_on_root_exp T H (M.weight i) (M.weight_nonzero i) Exp hExp realize
    l hl hL hbound ⟨M.letter i, M.letter_root i⟩ t

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootSwitchBounds
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient bounds for root switches at a Cartan position

Conjugating a root displacement back from its Cartan position removes its
scalar weight, up to the proved polynomial nilpotent correction. Applying
actual root distortion gives the logarithmic switch estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

/-- A switch on a translated right-positioned sheet is measured by its
conjugate displacement. -/
theorem dist_right_switch {G : Type*} [Group G] [PseudoMetricSpace G]
    [IsIsometricSMul G G] (x n d : G) :
    dist (x * d) (x * n * d) = dist 1 (d⁻¹ * n * d) := by
  calc
    _ = dist d (n * d) := by simpa only [mul_assoc] using dist_mul_left x d (n * d)
    _ = _ := by simpa only [inv_mul_cancel, mul_assoc] using
      (dist_mul_left d⁻¹ d (n * d)).symm

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- The ambient switch estimate, retaining the full nilpotent correction
and the exponential scalar contraction at the Cartan position. -/
theorem root_switch_bound_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (x : G) (h : H) (v : rootSpace H χ),
      dist (x * Exp h) (x * Exp v * Exp h) ≤
        D * Real.log (2 + C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^
          finrank ℝ (rootSpace H χ) * Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖) := by
  obtain ⟨D, hD, hdist⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  obtain ⟨C, hC, hbound⟩ := exists_rootAction_exp_bound H χ
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  refine ⟨C, D, hC, hD, ?_⟩
  intro x h v
  let w : rootSpace H χ := NormedSpace.exp (rootAction H χ (-h)) v
  have hw : Exp w = (Exp h)⁻¹ * Exp v * Exp h := by
    have hneg : j ((-h : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = -j h := by
      change j (-(h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
      exact map_neg j _
    have hr := represented_root_exp_conjugation H χ j (-h) 1 v
    simp only [one_smul, hneg] at hr
    apply hρ
    rw [map_mul, map_mul, map_inv, hmatch, hmatch, hmatch]
    change algebraExpUnit (j (w : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [algebraExpUnit_neg] at hr
    simpa only [w, inv_inv] using hr
  have hn : ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (-(χ h)) * ‖(rootCoordinates H χ) v‖ := by
    have hb := hbound (-h) v
    change ‖(rootCoordinates H χ) w‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun (-h)‖) ^ finrank ℝ (rootSpace H χ) *
        Real.exp (χ (-h)) * ‖(rootCoordinates H χ) v‖ at hb
    simpa only [map_neg, norm_neg] using hb
  rw [dist_right_switch, ← hw]
  apply (hdist w).trans
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (by linarith [hn])) hD.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootSupportSwitch
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmically short switches at supporting positions

A linearly bounded Cartan position and a bounded contracted amplitude give
a switch of length `O(log (2 + r))`. The constants are independent of the
translated sheet and the particular supporting position.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- The root-switch estimate in the exact support regime. The hypothesis on
the contracted amplitude is satisfied by `|t| ≤ B exp (χ h)`. -/
theorem logarithmic_root_support_switch_polynomial_position
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r → ∀ (x : G) (h : H) (t : ℝ),
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      |t| * Real.exp (-(χ h)) ≤ B →
      dist (x * Exp h) (x * Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤
        K * Real.log (2 + r) := by
  obtain ⟨C, D, hC, hD, hs⟩ := root_switch_bound_of_published_realization
    T H χ hχ Exp hExp realize
  let d := finrank ℝ (rootSpace H χ)
  let M := C * B * ‖(rootCoordinates H χ) v‖ * (1 + A) ^ d
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  let q := ((p * d : ℕ) : ℝ) + Real.log (2 + M) / Real.log 2
  have hq : 0 < q := by
    have hn : (0 : ℝ) ≤ (p * d : ℕ) := Nat.cast_nonneg (p * d)
    have hp : 0 < Real.log (2 + M) / Real.log 2 :=
      div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
    dsimp [q]
    linarith
  refine ⟨D * q, mul_pos hD hq, ?_⟩
  intro r hr x h t hh ht
  have hbase : 1 + ‖(finBasis ℝ H).equivFun h‖ ≤ (1 + A) * (1 + r) ^ p := by
    have hp : 1 ≤ (1 + r) ^ p := one_le_pow₀ (by linarith)
    nlinarith
  have hinside :
      C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d * Real.exp (-(χ h)) *
        ‖(rootCoordinates H χ) (t • v)‖ ≤ M * (1 + r) ^ (p * d) := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ = C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
          (|t| * Real.exp (-(χ h))) * ‖(rootCoordinates H χ) v‖ := by ring
      _ ≤ C * ((1 + A) * (1 + r) ^ p) ^ d * B * ‖(rootCoordinates H χ) v‖ := by
        gcongr
      _ = M * (1 + r) ^ (p * d) := by dsimp [M]; rw [mul_pow, pow_mul]; ring
  have hs' := hs x h (t • v)
  apply hs'.trans
  calc
    _ ≤ D * Real.log (2 + M * (1 + r) ^ (p * d)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.log_le_log (by positivity) (by linarith [hinside])
    _ ≤ D * (q * Real.log (2 + r)) :=
      mul_le_mul_of_nonneg_left (log_two_add_polynomial_le hM hr (p * d)) hD.le
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSupportSwitch
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One switch constant for the actual Cartan alphabet

The finite family of nonzero root generators admits one logarithmic switch
bound. At a supporting position, the large generator amplitude cancels the
scalar part of the adjoint action exactly.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
include T in
/-- Uniformly short supporting switches for every letter in the constructed
Cartan word model, including its generalized-root nilpotent corrections. -/
theorem exists_uniform_support_switch_bound
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin M.letterCount) (r : ℝ), 0 ≤ r →
      ∀ (x : G) (h : H) (s t : ℝ),
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      M.weight i h = r * s → |t| ≤ B * Real.exp (r * s) →
      dist (x * Exp h) (x * Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤
        K * Real.log (2 + r) := by
  classical
  let X (i : Fin M.letterCount) : rootSpace H (M.weight i) :=
    ⟨M.letter i, M.letter_root i⟩
  choose K hK hb using (fun i : Fin M.letterCount =>
    logarithmic_root_support_switch_polynomial_position T H (M.weight i)
      (M.weight_nonzero i) Exp hExp realize (X i) hA hB p)
  let K' := 1 + ∑ i, K i
  have hnonneg i : 0 ≤ K i := (hK i).le
  have hK' : 0 < K' := by
    have hh : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hnonneg i)
    dsimp [K']
    linarith
  refine ⟨K', hK', ?_⟩
  intro i r hr x h s t hh hs ht
  have hcancel : |t| * Real.exp (-(M.weight i h)) ≤ B := by
    rw [hs]
    have ht' := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-(r * s))).le
    have he : Real.exp (r * s) * Real.exp (-(r * s)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simpa only [mul_assoc, he, mul_one] using ht'
  have hki : K i ≤ K' := by
    have hi : K i ≤ ∑ j, K j :=
      Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    dsimp [K']
    linarith
  exact (hb i r hr x h t hh hcancel).trans
    (mul_le_mul_of_nonneg_right hki (Real.log_nonneg (by linarith)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootSwitchCurves
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous short switches with constant height

Use the actual root one-parameter subgroup for a switch. Every pair of its
points has logarithmic distance at a supporting Cartan position, while its
canonical height is exactly constant. No choice of geodesics is needed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

include T hExp realize in
/-- One logarithmic diameter bound for all actual root switch curves. -/
theorem CartanWordModel.exists_uniform_support_switch_curve_bound
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin M.letterCount) (r : ℝ), 0 ≤ r →
      ∀ (x : G) (h : H) (s b : ℝ),
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      M.weight i h = r * s → |b| ≤ B * Real.exp (r * s) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      dist (rootSwitchCurve Exp (M.letter i) b x (Exp h) t)
        (rootSwitchCurve Exp (M.letter i) b x (Exp h) u) ≤ K * Real.log (2 + r) := by
  obtain ⟨K, hK, hb⟩ := M.exists_uniform_support_switch_bound T Exp hExp realize hA hB p
  refine ⟨K, hK, ?_⟩
  intro i r hr x h s b hh hs hb' t ht u hu
  have hsub : |u - t| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, ht.2], by linarith [hu.2, ht.1]⟩
  have hamp : |(u - t) * b| ≤ B * Real.exp (r * s) := by
    rw [abs_mul]
    calc
      |u - t| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right hsub (abs_nonneg b)
      _ ≤ B * Real.exp (r * s) := by simpa using hb'
  have he : Exp ((u * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
      Exp ((t * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
        Exp (((u - t) * b) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    rw [← hExp.map_add_smul]
    congr 2
    ring
  have h := hb i r hr (x * Exp ((t * b) • (M.letter i :
    GroupLieAlgebra (𝓘(ℝ, EG)) G))) h s ((u - t) * b) hh hs hamp
  simpa only [rootSwitchCurve, he, mul_assoc] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateVisits
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan support visits for finitely many prescribed template directions

The directions are actual Cartan vectors. A convex target containing their
images contains every support path, including the short root switches.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold BigOperators

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

set_option maxHeartbeats 1000000 in
include T hExp realize hl hL hbound in
/-- One common metric bound for the finite family of support directions.
Every value under the homomorphism lies exactly in the scaled target. -/
theorem exists_template_support_visit_bound
    (v : Fin M.letterCount → H) (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ n : G, l n = 1 →
      ∀ (i : Fin M.letterCount) (b : ℝ),
      |b| ≤ B * Real.exp (r * M.weight i (v i)) →
      ∃ γ : Path (n * 1) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        (∀ t, ∃ z ∈ E,
          (l (γ t)).toAdd = r • z) ∧
        γ = M.templateVisitPath T hExp realize v i n r b := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let δ i := v i
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (δ i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hdmul i s t : d i (s + t) = d i s * d i t := hExp.map_add_smul _ s t
  have hld i t : (l (d i t)).toAdd = t • ((l (Exp (δ i))).toAdd - 0) := by
    simpa [d] using hom_flow_eq_smul (d i) (hd i) (hd₀ i) (hdmul i) l hl t
  have hmem i : (l (Exp (δ i))).toAdd ∈ E := hvE i
  choose C hC hvisit using (fun i => supportVisitPath_uniform_bound l (d i) (hd i)
    (hd₀ i) (hdmul i) hE hE0 (hmem i) (hld i))
  let A := ∑ j, ‖(finBasis ℝ H).equivFun (v j)‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv i : ‖(finBasis ℝ H).equivFun (v i)‖ ≤ A :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((finBasis ℝ H).equivFun (v j)))
      (Finset.mem_univ i)
  obtain ⟨K, hK, hswitch⟩ := M.exists_uniform_support_switch_curve_bound T Exp hExp
    realize hA hB 1
  let C' := 4 * (1 + (∑ i, C i) + K)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hC' : 0 ≤ C' := by dsimp [C'] <;> positivity
  have hCi i : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨C', hC', ?_⟩
  intro r hr n hn i b hb
  let f (t : ℝ) := Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hf : Continuous f := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf₀ : f 0 = 1 := by simp [f, hExp.map_zero]
  have hlf t : l (f t) = 1 := M.hom_eq_one_on_letter T hExp realize l hl hL hbound i t
  have hnorm : ‖(finBasis ℝ H).equivFun (r • δ i)‖ ≤ A * (1 + r) ^ 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, pow_one]
    have hbδ := hv i
    change r * ‖(finBasis ℝ H).equivFun (v i)‖ ≤ A * (1 + r)
    nlinarith
  have hweight : M.weight i (r • δ i) = r * M.weight i (v i) := by
    rw [map_smul, smul_eq_mul]
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hdiam u (hu : u ∈ Set.Icc (0 : ℝ) 1) t (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dist (n * f (u * b) * (1 * d i r)) (n * f (t * b) * (1 * d i r)) ≤
        K * Real.log (2 + r) := by
    have hh := hswitch i r hr n (r • δ i) (M.weight i (v i)) b
      hnorm hweight hb u hu t ht
    simpa only [rootSwitchCurve, one_mul, SetLike.val_smul, d, f] using hh
  obtain ⟨hγ, hγheight⟩ := hvisit i r hr n 1 hn (by simp) f hf hf₀ hlf b
    (K * Real.log (2 + r)) (mul_nonneg hK.le hlog) hdiam
  refine ⟨supportVisitPath (d i) (hd i) (hd₀ i) f hf hf₀ n 1 r b,
    hγ.mono ?_ ?_, hγheight, rfl⟩
  · apply mul_le_mul_of_nonneg_right _ hr
    dsimp [C']
    nlinarith [hCi i]
  · dsimp [C']
    nlinarith [hCi i, mul_nonneg (sub_nonneg.mpr (hCi i)) hlog,
      mul_nonneg hsum hlog]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateWordPath
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specified template paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed template visits. This retains both measurable samples and the
uniform metric bounds needed for endpoint integration.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
/-- Uniform metric and homomorphism-height bounds for the specified paths. -/
theorem exists_templateWordPath_bound_oai [IsIsometricSMul G G]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : Fin M.letterCount → H) (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N → (∀ z ∈ u, |z.2| ≤ B) →
      PathMetricBound (M.templateWordPath T hExp realize v r u)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, ∃ z ∈ E,
        (l (M.templateWordPath T hExp realize v r u t)).toAdd = r • z := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨C, hC, hvisit⟩ := M.exists_template_support_visit_bound T hExp realize l hl hL hbound v E hE hE0 hvE hB
  refine ⟨C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro r hr u hu hub
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let P i b := |b| ≤ B * Real.exp (r * M.weight i (v i))
  let S : Set G := {g | ∃ z ∈ E, (l g).toAdd = r • z}
  have hbase n (hn : l n = 1) : n * 1 ∈ S := by
    exact ⟨0, hE0, by simp [hn]⟩
  have hstep n (hn : l n = 1) i b (hb : P i b) :
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n 1 r b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n 1 r b t ∈ S := by
    obtain ⟨γ, hγ, hheight, he⟩ := hvisit r hr n hn i b hb
    subst γ
    exact ⟨hγ, hheight⟩
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  have hscaled : ∀ z ∈ M.templateScaledWord v r u, P z.1 z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    dsimp [P]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hub q hq) (Real.exp_pos _).le
  obtain ⟨hb, hh⟩ := supportWordPath_bound d f hd hf hd₀ hf₀ 1 r l P
    (fun i b _ => M.hom_eq_one_on_letter T hExp realize l hl hL hbound i b)
    hbase (mul_nonneg hC hr) (mul_nonneg hC hlog) hstep
    (M.templateScaledWord v r u) hscaled 1 (map_one l)
  have hp : (2 : ℝ) ^ (M.templateScaledWord v r u).length ≤ 2 ^ N := by
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [templateScaledWord, List.length_map] using hu
  have hb' := hb.mono
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hr))
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hlog))
  constructor
  · change PathMetricBound
      (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.templateScaledWord v r u) 1)
      ((C * 2 ^ N) * r) ((C * 2 ^ N) * (1 + Real.log (2 + r)))
    first | (convert hb' using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hb'.trans (le_of_eq (by ring)))
  · exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound_oai.{u_1, u_2, u_3} := @OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound_oai.{u_1, u_2, u_3}
