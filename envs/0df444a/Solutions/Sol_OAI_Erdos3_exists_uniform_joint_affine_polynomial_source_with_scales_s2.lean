-- Prove2me | solution 1 for OAI.Erdos3.exists_uniform_joint_affine_polynomial_source_with_scales_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:08.73032+00:00
-- url     : https://prove2.me/submissions/6bebda5e-9f56-4810-ad32-13a7955748b6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113
import Theorems.Thm_OAI_Erdos3_exists_canonical_joint_affine_good_mass_s2
import Theorems.Thm_OAI_Erdos3_jointAffineBoolean_good_weight_comparison_s2
import Theorems.Thm_OAI_Erdos3_jointAffineBoolean_regularization_error_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_section_integrable {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ C t) (x : X) :
    Integrable (fun t => F t x) μ :=
  hC.mono' (hm x) (hbound.mono (fun _ ht => ht x))

theorem densityMixture_cap {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, F t x ∈ Set.Icc (0 : ℝ) (C t)) (x : X) :
    densityMixture μ F x ∈ Set.Icc (0 : ℝ) (∫ t, C t ∂μ) := by
  have hb : ∀ᵐ t ∂μ, ∀ y, ‖F t y‖ ≤ C t := hbound.mono fun t ht y => by
    rw [Real.norm_of_nonneg (ht y).1]
    exact (ht y).2
  exact ⟨integral_nonneg_of_ae (hbound.mono (fun _ ht => (ht x).1)),
    integral_mono_ae (densityMixture_section_integrable μ F C hC hm hb x) hC
      (hbound.mono (fun _ ht => (ht x).2))⟩

theorem densityMixture_lipschitz {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) (F : T → X → ℝ) (L : T → ℝ≥0)
    (hL : Integrable (fun t => (L t : ℝ)) μ)
    (hint : ∀ x, Integrable (fun t => F t x) μ)
    (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) :
    LipschitzWith ⟨∫ t, (L t : ℝ) ∂μ, integral_nonneg (fun t => (L t).coe_nonneg)⟩
      (densityMixture μ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, F t x ∂μ) - ∫ t, F t y ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hb : ∀ᵐ t ∂μ, ‖F t x - F t y‖ ≤ (L t : ℝ) * dist x y := by
    filter_upwards [hLip] with t ht
    simpa only [Real.dist_eq, Real.norm_eq_abs] using ht.dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hL.mul_const (dist x y)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_uniform_bound {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → X → ℝ) (C L : ℝ≥0)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hF : ∀ᵐ t ∂μ, (∀ x, F t x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (F t)) :
    (∀ x, densityMixture μ F x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (densityMixture μ F) := by
  have hb : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ (C : ℝ) := by
    filter_upwards [hF] with t ht
    intro x
    rw [Real.norm_of_nonneg (ht.1 x).1]
    exact (ht.1 x).2
  have hi := densityMixture_section_integrable μ F (fun _ => (C : ℝ)) (integrable_const _) hm hb
  constructor
  · intro x
    have h := densityMixture_cap μ F (fun _ => (C : ℝ)) (integrable_const _) hm
      (hF.mono (fun _ ht => ht.1)) x
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := densityMixture_lipschitz μ F (fun _ => L) (integrable_const _) hi
      (hF.mono (fun _ ht => ht.2))
    have heq : (⟨∫ _ : T, (L : ℝ) ∂μ, integral_nonneg (fun _ => L.coe_nonneg)⟩ : ℝ≥0) = L := by
      apply Subtype.ext
      simp
    rw [heq] at h
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_contDiff [Fintype O] (c : B → ℝ) (sets : O → Finset α) :
    ContDiff ℝ ∞ (booleanSamplerMap (F := F) c sets) :=
  contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (booleanSamplerPolynomial c (sets o)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productMinorEntryBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorEntryBound q h C R := by
  unfold productMinorEntryBound
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productMinorPartialBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorPartialBound q h C R := by
  unfold productMinorPartialBound
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem productMinorDeterminantDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorDeterminantDerivativeBound n j q h C R := by
  have he := productMinorEntryBound_nonneg q h hC hR
  have hd := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDeterminantDerivativeBound
  positivity

end Erdos3

end

section

namespace Erdos3

theorem boolean_minor_parameter_count_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] {h : ℕ} (hh : 0 < h) :
    0 < Fintype.card O * (h * (Fintype.card α + 1)) :=
  Nat.mul_pos Fintype.card_pos (Nat.mul_pos hh (Nat.succ_pos _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductBoundaryRadius_pos (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) : 0 < scalarCubeProductBoundaryRadius ι α η :=
  div_pos hη (mul_pos (scalarCubeBoundaryConstant_pos α) (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem operatorPrecompose_norm_le (J : E →L[ℝ] X) :
    ‖operatorPrecompose (Y := Y) J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J)
  intro A
  exact (A.opNorm_comp_le J).trans_eq (mul_comm _ _)

theorem affineSlice_fderiv (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) :
    fderiv ℝ (fun y => F (c + J y)) x = (fderiv ℝ F (c + J x)).comp J := by
  exact (hF.hasFDerivAt.comp x (J.hasFDerivAt.const_add c)).fderiv

theorem affineSlice_fderiv_norm_le (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) (hJ : ‖J‖ ≤ 1) {H : ℝ}
    (hH : ‖fderiv ℝ F (c + J x)‖ ≤ H) :
    ‖fderiv ℝ (fun y => F (c + J y)) x‖ ≤ H := by
  rw [affineSlice_fderiv F c J x hF]
  calc
    _ ≤ ‖fderiv ℝ F (c + J x)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ H * 1 := mul_le_mul hH hJ (norm_nonneg J) ((norm_nonneg _).trans hH)
    _ = H := mul_one H

theorem affineSlice_second_fderiv_norm_le (F : X → Y) (hF : ContDiff ℝ 2 F)
    (c : X) (J : E →L[ℝ] X) (x : E) (hJ : ‖J‖ ≤ 1) {H : ℝ}
    (hH : ‖fderiv ℝ (fderiv ℝ F) (c + J x)‖ ≤ H) :
    ‖fderiv ℝ (fderiv ℝ (fun y => F (c + J y))) x‖ ≤ H := by
  let L : (X →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Y) := operatorPrecompose J
  let g : E → (X →L[ℝ] Y) := fun y => fderiv ℝ F (c + J y)
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hg := ((hD.differentiable one_ne_zero (c + J x)).hasFDerivAt.comp x
    (J.hasFDerivAt.const_add c))
  have hg' : HasFDerivAt g ((fderiv ℝ (fderiv ℝ F) (c + J x)).comp J) x := hg
  have he : fderiv ℝ (fun y => F (c + J y)) = L ∘ g := by
    funext y
    exact affineSlice_fderiv F c J y (hF.differentiable (by norm_num) _)
  rw [he, fderiv_comp x L.differentiableAt hg'.differentiableAt, L.fderiv, hg'.fderiv]
  have hL : ‖L‖ ≤ 1 := (operatorPrecompose_norm_le J).trans hJ
  have hinner : ‖(fderiv ℝ (fderiv ℝ F) (c + J x)).comp J‖ ≤ H := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ F) (c + J x)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ H * 1 := mul_le_mul hH hJ (norm_nonneg J)
        ((norm_nonneg (fderiv ℝ (fderiv ℝ F) (c + J x))).trans hH)
      _ = H := mul_one H
  calc
    _ ≤ ‖L‖ * ‖(fderiv ℝ (fderiv ℝ F) (c + J x)).comp J‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * H := mul_le_mul hL hinner
      (norm_nonneg ((fderiv ℝ (fderiv ℝ F) (c + J x)).comp J)) zero_le_one
    _ = H := one_mul H

end Erdos3

end

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem second_fderiv_sub (F G : X → Y) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (x : X) :
    fderiv ℝ (fderiv ℝ (fun y => F y - G y)) x =
      fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x := by
  have he : fderiv ℝ (fun y => F y - G y) = fun y => fderiv ℝ F y - fderiv ℝ G y := by
    funext y
    exact fderiv_sub (hF.differentiable (by norm_num) y) (hG.differentiable (by norm_num) y)
  rw [he]
  exact fderiv_sub ((hF.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x)
    ((hG.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x)

theorem affineSlice_first_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖fderiv ℝ F (b + J x) - fderiv ℝ G (b + J x)‖ ≤ ε) :
    ‖fderiv ℝ (fun y => F (b + J y)) x - fderiv ℝ (fun y => G (b + J y)) x‖ ≤ ε := by
  rw [affineSlice_fderiv F b J x (hF.differentiable (by norm_num) _),
    affineSlice_fderiv G b J x (hG.differentiable (by norm_num) _), ← ContinuousLinearMap.sub_comp]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hJ)).trans herr

theorem affineSlice_second_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖fderiv ℝ (fderiv ℝ F) (b + J x) - fderiv ℝ (fderiv ℝ G) (b + J x)‖ ≤ ε) :
    ‖fderiv ℝ (fderiv ℝ (fun y => F (b + J y))) x -
      fderiv ℝ (fderiv ℝ (fun y => G (b + J y))) x‖ ≤ ε := by
  have hs : ‖fderiv ℝ (fderiv ℝ (fun y => F y - G y)) (b + J x)‖ ≤ ε := by
    rw [second_fderiv_sub F G hF hG]
    exact herr
  have ht := affineSlice_second_fderiv_norm_le (fun y => F y - G y) (hF.sub hG) b J x hJ hs
  have hFs : ContDiff ℝ 2 (fun y => F (b + J y)) := hF.comp (contDiff_const.add J.contDiff)
  have hGs : ContDiff ℝ 2 (fun y => G (b + J y)) := hG.comp (contDiff_const.add J.contDiff)
  rw [second_fderiv_sub (fun y => F (b + J y)) (fun y => G (b + J y)) hFs hGs] at ht
  exact ht

theorem affineSlice_c2_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖F (b + J x) - G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ F (b + J x) - fderiv ℝ G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ F) (b + J x) - fderiv ℝ (fderiv ℝ G) (b + J x)‖ ≤ ε) :
    ‖F (b + J x) - G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ (fun y => F (b + J y)) x - fderiv ℝ (fun y => G (b + J y)) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => F (b + J y))) x -
        fderiv ℝ (fderiv ℝ (fun y => G (b + J y))) x‖ ≤ ε :=
  ⟨herr.1, affineSlice_first_difference_bound F G hF hG b J hJ x herr.2.1,
    affineSlice_second_difference_bound F G hF hG b J hJ x herr.2.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_support_card_le_fintype {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ Fintype.card I := by
  classical
  let f : p.support → (I → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hd i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem mvPolynomial_unit_box_bound {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ (d + 1 : ℝ) ^ Fintype.card I * C := by
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ Fintype.card I := by
    exact_mod_cast mvPolynomial_support_card_le_fintype p hd
  calc
    _ ≤ ∑ m ∈ p.support, |p.coeff m| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _m ∈ p.support, C := Finset.sum_le_sum (fun m _ => hc m)
    _ = (p.support.card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

theorem mvPolynomial_pderiv_coeff_bound {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) {d : ℕ} (hd : p.degreeOf j ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C) (m : I →₀ ℕ) :
    |(MvPolynomial.pderiv j p).coeff m| ≤ (d : ℝ) * C := by
  rw [MvPolynomial.coeff_pderiv]
  by_cases hz : p.coeff (m + Finsupp.single j 1) = 0
  · rw [hz, zero_mul, abs_zero]
    positivity
  · have hd' := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hz)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hd'
    have hdR : (m j + 1 : ℝ) ≤ d := by exact_mod_cast hd'
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m j + 1)]
    exact (mul_le_mul (hc _) hdR (by positivity) hC).trans_eq (mul_comm C d)

theorem mvPolynomial_pderiv_unit_box_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) (j : I) :
    |MvPolynomial.eval x (MvPolynomial.pderiv j p)| ≤
      (d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C) :=
  mvPolynomial_unit_box_bound _ (fun i => mvPolynomial_pderiv_degreeOf_le p j i (hd i))
    (by positivity) (mvPolynomial_pderiv_coeff_bound p j (hd j) hC hc) x hx

theorem mvPolynomial_second_pderiv_unit_box_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) (j k : I) :
    |MvPolynomial.eval x (MvPolynomial.pderiv k (MvPolynomial.pderiv j p))| ≤
      (d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * ((d : ℝ) * C)) :=
  mvPolynomial_pderiv_unit_box_bound _ (fun i => mvPolynomial_pderiv_degreeOf_le p j i (hd i))
    (by positivity) (mvPolynomial_pderiv_coeff_bound p j (hd j) hC hc) x hx k

end Erdos3

end

section

namespace Erdos3

theorem polynomialOperator_fderiv_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) (j : I) (row : O) (col : J) :
    (fderiv ℝ A x (Pi.single j 1)) (Pi.single col 1) row =
      MvPolynomial.eval x (MvPolynomial.pderiv j (p row col)) := by
  have hscalar : (fun y => A y (Pi.single col 1) row) =
      (fun y => MvPolynomial.eval y (p row col)) := funext (fun y => hentry y row col)
  have hB : DifferentiableAt ℝ (fun y => A y (Pi.single col 1)) x :=
    hA.clm_apply (differentiableAt_const _)
  have hp := mvPolynomial_fderiv_coordinate (p row col) x j
  rw [← hscalar, fderiv_apply hB row, fderiv_clm_apply hA (differentiableAt_const _)] at hp
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply] at hp
  exact hp

theorem polynomialOperator_fderiv_norm_le {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ row col j, |MvPolynomial.eval x (MvPolynomial.pderiv j (p row col))| ≤ M) :
    ‖fderiv ℝ A x‖ ≤ Fintype.card I * (Fintype.card J * M) := by
  apply clm_norm_le_card_mul_of_basis _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro j
  apply clm_norm_le_card_mul_of_entries _ hM
  intro col row
  rw [polynomialOperator_fderiv_entry A p hentry x hA j row col]
  exact hp row col j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_mod_single_support {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) {m : I →₀ ℕ}
    (hm : m ∈ (p.modMonomial (Finsupp.single j 1)).support) : m j = 0 := by
  by_contra hz
  have hle : Finsupp.single j 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hz)
  exact MvPolynomial.mem_support_iff.mp hm (MvPolynomial.coeff_modMonomial_of_le p hle)

theorem mvPolynomial_eval_update_of_support_zero {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) (hp : ∀ m ∈ p.support, m j = 0)
    (x : I → ℝ) (t : ℝ) : MvPolynomial.eval (Function.update x j t) p = MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    rw [hp m hm, pow_zero, pow_zero]
  · rw [Function.update_of_ne hi]

theorem mvPolynomial_eval_sub_zero_coordinate {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) (x : I → ℝ) :
    MvPolynomial.eval x p - MvPolynomial.eval (Function.update x j 0) p =
      x j * MvPolynomial.eval x (p.divMonomial (Finsupp.single j 1)) := by
  have h := congrArg (MvPolynomial.eval x) (p.divMonomial_add_modMonomial_single j)
  have h0 := congrArg (MvPolynomial.eval (Function.update x j 0))
    (p.divMonomial_add_modMonomial_single j)
  simp only [map_add, map_mul, MvPolynomial.eval_X, Function.update_self, zero_mul, zero_add] at h h0
  rw [mvPolynomial_eval_update_of_support_zero _ j
    (fun m hm => mvPolynomial_mod_single_support p j hm) x 0] at h0
  linarith

theorem mvPolynomial_div_single_degreeOf_le {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    (p.divMonomial (Finsupp.single j 1)).degreeOf i ≤ d := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : p.coeff (Finsupp.single j 1 + m) ≠ 0 := by
    simpa only [MvPolynomial.coeff_divMonomial] using MvPolynomial.mem_support_iff.mp hm
  have hb := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hc)
  have hi : m i ≤ (Finsupp.single j 1 + m : I →₀ ℕ) i := by simp only [Finsupp.add_apply]; omega
  exact hi.trans hb

theorem mvPolynomial_div_single_coeff_bound {I : Type*}
    (p : MvPolynomial I ℝ) (j : I) {C : ℝ} (hc : ∀ m, |p.coeff m| ≤ C) (m : I →₀ ℕ) :
    |(p.divMonomial (Finsupp.single j 1)).coeff m| ≤ C := by
  rw [MvPolynomial.coeff_divMonomial]
  exact hc _

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

omit [DecidableEq I] in
theorem polynomialVectorMap_norm_bound (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ (d + 1 : ℝ) ^ Fintype.card I * C := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro o
  exact mvPolynomial_unit_box_bound (p o) (hd o) hC (hc o) x hx

theorem polynomialVectorMap_fderiv_bound (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤
      Fintype.card I * ((d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C)) := by
  apply clm_norm_le_card_mul_of_entries _ (by positivity)
  intro i o
  rw [polynomialVectorMap_fderiv_entry]
  exact mvPolynomial_pderiv_unit_box_bound (p o) (hd o) hC (hc o) x hx i

theorem polynomialVectorMap_second_fderiv_bound [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
      Fintype.card I * (Fintype.card I *
        ((d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * ((d : ℝ) * C)))) := by
  have hs : ContDiff ℝ 2 (polynomialVectorMap p) := contDiff_infty.mp (polynomialVectorMap_contDiff p) 2
  have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
  have hA := hs'.differentiable one_ne_zero x
  exact polynomialOperator_fderiv_norm_le _ (fun o i => MvPolynomial.pderiv i (p o))
    (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x hA (by positivity)
    (fun o i j => mvPolynomial_second_pderiv_unit_box_bound (p o) (hd o) hC (hc o) x hx i j)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem polynomialParameterPoint_affine {Z I : Type*} [Fintype I]
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    polynomialParameterPoint t z x = polynomialParameterPoint t z 0 + polynomialParameterInjection Z I x := by
  ext s
  rcases s with _ | (j | i) <;> simp [polynomialParameterPoint, polynomialParameterInjection]

theorem polynomialParameterInjection_norm_le (Z I : Type*) [Fintype Z] [Fintype I] :
    ‖polynomialParameterInjection Z I‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro s
  rcases s with _ | (j | i)
  · simp [polynomialParameterInjection]
  · simp [polynomialParameterInjection]
  · simpa [polynomialParameterInjection] using norm_le_pi_norm x i

theorem polynomialParameterPoint_unit_box {Z I : Type*} {t : ℝ} (ht : |t| ≤ 1)
    {z : Z → ℝ} (hz : ∀ i, |z i| ≤ 1) {x : I → ℝ} (hx : ∀ i, |x i| ≤ 1)
    (s : PolynomialParameter Z I) : |polynomialParameterPoint t z x s| ≤ 1 := by
  rcases s with _ | (j | i)
  · exact ht
  · exact hz j
  · exact hx i

theorem parameterPolynomialMap_contDiff {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) :
    ContDiff ℝ ∞ (parameterPolynomialMap p t z) := by
  have he : parameterPolynomialMap p t z =
      fun x => polynomialVectorMap p (polynomialParameterPoint t z 0 + polynomialParameterInjection Z I x) :=
    funext (fun x => congrArg (polynomialVectorMap p) (polynomialParameterPoint_affine t z x))
  rw [he]
  exact (polynomialVectorMap_contDiff p).comp (contDiff_const.add (polynomialParameterInjection Z I).contDiff)

theorem parameterPolynomialMap_sub_zero {Z I O : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype I] [DecidableEq I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x =
      t • parameterPolynomialMap (fun o => (p o).divMonomial (Finsupp.single none 1)) t z x := by
  ext o
  have he : Function.update (polynomialParameterPoint t z x) none 0 = polynomialParameterPoint 0 z x := by
    funext s
    rcases s with _ | (j | i) <;> simp [polynomialParameterPoint]
  have ht := mvPolynomial_eval_sub_zero_coordinate (p o) none (polynomialParameterPoint t z x)
  rw [he] at ht
  exact ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

theorem sigmaAxisSampler_contDiff (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, ContDiff ℝ ∞ (U d)) : ContDiff ℝ ∞ (sigmaAxisSampler U) :=
  contDiff_pi.mpr (fun s => ((contDiff_apply ℝ ℝ s.2).comp (hU s.1)).comp
    (sigmaAxisProjection I s.1).contDiff)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] in
theorem jointBooleanSampler_contDiff (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) : ContDiff ℝ ∞ (jointBooleanSampler h c sets) :=
  sigmaAxisSampler_contDiff _ (fun d => booleanSamplerMap_contDiff (c d) (sets d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredC2Difference
namespace OAI

section

namespace Erdos3

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem factoredDifference_fderiv (F G R : E → Y) (t : ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (hR : Differentiable ℝ R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ F x - fderiv ℝ G x = t • fderiv ℝ R x := by
  rw [← fderiv_sub (hF x) (hG x), show F - G = t • R from funext he,
    fderiv_const_smul (hR x)]

theorem factoredDifference_second_fderiv (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x = t • fderiv ℝ (fderiv ℝ R) x := by
  have hF' : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hG' : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hR' : ContDiff ℝ 1 (fderiv ℝ R) := hR.fderiv_right (by norm_num)
  exact factoredDifference_fderiv _ _ _ t (hF'.differentiable one_ne_zero)
    (hG'.differentiable one_ne_zero) (hR'.differentiable one_ne_zero)
    (factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
      (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he) x

theorem factoredDifference_c2_bounds (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) {B₀ B₁ B₂ : ℝ}
    (h₀ : ‖R x‖ ≤ B₀) (h₁ : ‖fderiv ℝ R x‖ ≤ B₁) (h₂ : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ B₂) :
    ‖F x - G x‖ ≤ |t| * B₀ ∧ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ |t| * B₁ ∧
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ |t| * B₂ := by
  rw [he x, factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he x,
    factoredDifference_second_fderiv F G R t hF hG hR he x]
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_smul_le t (R x)).trans (mul_le_mul_of_nonneg_left h₀ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ R x)).trans
      (mul_le_mul_of_nonneg_left h₁ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ (fderiv ℝ R) x)).trans
      (mul_le_mul_of_nonneg_left h₂ (abs_nonneg t))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

theorem parameterPolynomialMap_c2_bounds
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let N := Fintype.card (PolynomialParameter Z I)
    ‖parameterPolynomialMap p t z x‖ ≤ (d + 1 : ℝ) ^ N * C ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x‖ ≤
        N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x‖ ≤
        N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) := by
  have hb := polynomialParameterPoint_unit_box ht hz hx
  have he : parameterPolynomialMap p t z =
      fun y => polynomialVectorMap p (polynomialParameterPoint t z 0 + polynomialParameterInjection Z I y) :=
    funext (fun y => congrArg (polynomialVectorMap p) (polynomialParameterPoint_affine t z y))
  refine ⟨polynomialVectorMap_norm_bound p hd hC hc _ hb, ?_, ?_⟩
  · rw [he]
    apply affineSlice_fderiv_norm_le _ _ _ x
      ((polynomialVectorMap_contDiff p).differentiable (by norm_num) _)
      (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact polynomialVectorMap_fderiv_bound p hd hC hc _ hb
  · rw [he]
    apply affineSlice_second_fderiv_norm_le _ ((polynomialVectorMap_contDiff p).of_le (WithTop.coe_le_coe.2 le_top))
      _ _ x (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact polynomialVectorMap_second_fderiv_bound p hd hC hc _ hb

theorem parameterPolynomialMap_perturbation_bounds
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let N := Fintype.card (PolynomialParameter Z I)
    ‖parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x‖ ≤
      |t| * ((d + 1 : ℝ) ^ N * C) ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x - fderiv ℝ (parameterPolynomialMap p 0 z) x‖ ≤
        |t| * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C))) ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x -
          fderiv ℝ (fderiv ℝ (parameterPolynomialMap p 0 z)) x‖ ≤
        |t| * (N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C))))) := by
  let q := fun o => (p o).divMonomial (Finsupp.single none 1)
  have hq := parameterPolynomialMap_c2_bounds q
    (fun o i => mvPolynomial_div_single_degreeOf_le (p o) none i (hd o i)) hC
    (fun o m => mvPolynomial_div_single_coeff_bound (p o) none (hc o) m) ht z hz x hx
  exact factoredDifference_c2_bounds (parameterPolynomialMap p t z) (parameterPolynomialMap p 0 z)
    (parameterPolynomialMap q t z) t
    ((parameterPolynomialMap_contDiff p t z).of_le (WithTop.coe_le_coe.2 le_top))
    ((parameterPolynomialMap_contDiff p 0 z).of_le (WithTop.coe_le_coe.2 le_top))
    ((parameterPolynomialMap_contDiff q t z).of_le (WithTop.coe_le_coe.2 le_top))
    (parameterPolynomialMap_sub_zero p t z) x hq.1 hq.2.1 hq.2.2

end Erdos3

end

section

namespace Erdos3

theorem polynomialC2BoxBudget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialC2BoxBudget N d C := by unfold polynomialC2BoxBudget; positivity

theorem polynomialC2BoxBudget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (d + 1 : ℝ) ^ N * C ≤ polynomialC2BoxBudget N d C ∧
      N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) ≤ polynomialC2BoxBudget N d C ∧
      N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) ≤ polynomialC2BoxBudget N d C := by
  let x : ℝ := (N : ℝ) * d
  let a : ℝ := (d + 1 : ℝ) ^ N * C
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h0 : 1 ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h1 : x ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h2 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
  have hb : polynomialC2BoxBudget N d C = (1 + x) ^ 2 * a := by dsimp [polynomialC2BoxBudget, x, a]; ring
  rw [hb]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 ha
  · have he : N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) = x * a := by dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h1 ha
  · have he : N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) = x ^ 2 * a := by
      dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h2 ha

theorem parameterPolynomialMap_uniform_c2_error
    {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z I)) d C
    ‖parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x - fderiv ℝ (parameterPolynomialMap p 0 z) x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x -
        fderiv ℝ (fderiv ℝ (parameterPolynomialMap p 0 z)) x‖ ≤ |t| * M := by
  have h := parameterPolynomialMap_perturbation_bounds p hd hC hc ht z hz x hx
  have hb := polynomialC2BoxBudget_dominates (Fintype.card (PolynomialParameter Z I)) d hC
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hb.1 (abs_nonneg t)),
    h.2.1.trans (mul_le_mul_of_nonneg_left hb.2.1 (abs_nonneg t)),
    h.2.2.trans (mul_le_mul_of_nonneg_left hb.2.2 (abs_nonneg t))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

theorem cubeMinorProbabilityConstant_pos (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < cubeMinorProbabilityConstant O α h N d :=
  mul_pos (pow_pos (scalarCubeDomainDensity_pos α) _) (multivariateSublevelConstant_pos hN d)

theorem cubeMinorProbabilityScale_pos (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < cubeMinorProbabilityScale O N d c₀ := by
  unfold cubeMinorProbabilityScale
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem jointBooleanDerivativeBudget_le (h : D → ℕ) (C : D → ℝ) (d : D) :
    productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤
        jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C := by
  classical
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast (Finset.single_le_sum (f := fun e => Real.toNNReal
    (productMinorDerivativeBound (Fintype.card (BlockParameter (B e) (Fin (h e)) α))
      (Fintype.card (O e)) (Fintype.card α) (h e) (C e) 1))
        (fun _ _ => zero_le) (Finset.mem_univ d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem jointBooleanWeightBudget_nonneg (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    0 ≤ jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  apply Finset.sum_nonneg
  intro d _
  exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr d i)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg A.coe_nonneg (hκ d))
      (productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC d) zero_le_one)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalSliceBounds
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι]

theorem coordinateScaleEquiv_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {C : ℝ} (hC : 0 ≤ C) (hcap : ∀ i, |w i| ≤ C) :
    ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg x))).2
  intro i
  change ‖w i * x i‖ ≤ C * ‖x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hcap i) (norm_le_pi_norm x i) (norm_nonneg _) hC

theorem coordinateScaleEquiv_inverse_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ |w i|) :
    ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ δ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hδ.le)
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg x))).2
  intro i
  change ‖x i / w i‖ ≤ δ⁻¹ * ‖x‖
  rw [norm_div, Real.norm_eq_abs (w i), div_eq_mul_inv, mul_comm]
  exact mul_le_mul (inv_anti₀ hδ (hlow i)) (norm_le_pi_norm x i) (norm_nonneg _)
    (inv_nonneg.mpr hδ.le)

theorem coordinateScaleEquiv_scaled_inverse_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ |w i|) :
    δ * ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (coordinateScaleEquiv_inverse_norm_le w hw hδ hlow) hδ.le).trans_eq
    (mul_inv_cancel₀ hδ.ne')

theorem coordinateScaleEquiv_affine_box (b w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    (hbox : ∀ i, |b i| + |w i| ≤ 1) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∀ i, |(b + (coordinateScaleEquiv w hw).toContinuousLinearEquiv x) i| ≤ 1 := by
  intro i
  change |b i + w i * x i| ≤ 1
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact (add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (hx i))).trans (hbox i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineProductProfile_measurable_center {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (c x : Ω → I → ℝ) (w : I → ℝ)
    (hc : ∀ i, Measurable (fun a => c a i)) (hx : ∀ i, Measurable (fun a => x a i)) :
    Measurable (fun a => affineProductProfile (c a) w (x a)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (smoothProbabilityProfile_contDiff.continuous.measurable.comp
    (((hx i).sub (hc i)).div_const (w i)))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_probability {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, 0 ≤ regularizedImageDensity μ U δ x) ∧ Integrable (regularizedImageDensity μ U δ) ∧
      (∫ x, regularizedImageDensity μ U δ x) = 1 := by
  apply densityMixture_probability_density μ volume _ (regularizedImageDensity_joint_measurable U hU δ)
  exact Filter.Eventually.of_forall (fun a =>
    ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩)

theorem regularizedImageDensity_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, regularizedImageDensity μ U δ x ∈ Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card I : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip I δ) (regularizedImageDensity μ U δ) := by
  apply densityMixture_uniform_bound μ _ (δ⁻¹ ^ Fintype.card I) (affineProductProfileLip I δ)
  · intro x
    exact ((regularizedImageDensity_joint_measurable U hU δ).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro a
    refine ⟨?_, affineProductProfile_lipschitz (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl)⟩
    intro x
    have hn := affineProductProfile_nonneg (U a) (fun _ => (δ : ℝ)) (fun _ => hδ) x
    have hc := affineProductProfile_cap (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl) x
    rw [Real.norm_of_nonneg hn] at hc
    exact ⟨hn, hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineCubeMinorThreshold_pos (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < affineCubeMinorThreshold J O α h N d c₀ δ η :=
  polynomialSublevelThreshold_pos _ _
    (mul_nonneg (cubeMinorProbabilityConstant_pos O α h hN d).le (pow_nonneg (inv_nonneg.mpr hδ.le) _))
    (cubeMinorProbabilityScale_pos O N d hc₀).le hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

variable (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
  (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) (δ : D → ℝ)

omit decidableEqB decidableEqO in
theorem jointAffineBooleanSampler_contDiff
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] :
    ContDiff ℝ ∞ (jointAffineBooleanSampler c sets L b) :=
  sigmaAxisSampler_contDiff _ (fun d =>
    (booleanSamplerMap_contDiff (c d) (sets d)).comp (contDiff_const.add (L d).contDiff))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

omit decidableEqB decidableEqO in
theorem jointAffineBoolean_c2_error_transport
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    {ε : ℝ} (herr : ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ ε) :
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => b s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V (slice x) - jointAffineBooleanSampler c sets L b x‖ ≤ ε ∧
      ‖fderiv ℝ (V ∘ slice) x - fderiv ℝ (jointAffineBooleanSampler c sets L b) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ (V ∘ slice)) x -
        fderiv ℝ (fderiv ℝ (jointAffineBooleanSampler c sets L b)) x‖ ≤ ε := by
  intro slice x hx
  let b₀ : JointBlockParameter B h α → ℝ := fun s => b s.1 s.2
  let L₀ := sigmaAxisOperator (fun d => (L d).toContinuousLinearMap)
  have hnorm : ‖L₀‖ ≤ 1 := sigmaAxisOperator_norm_le _ zero_le_one hL
  have hbx (s : JointBlockParameter B h α) : |(b₀ + L₀ x) s| ≤ 1 :=
    hbox s.1 (fun i => x ⟨s.1, i⟩) (fun i => hx ⟨s.1, i⟩) s.2
  have ht := affineSlice_c2_difference_bound V (jointBooleanSampler h c sets) hV
    ((jointBooleanSampler_contDiff h c sets).of_le (WithTop.coe_le_coe.2 le_top)) b₀ L₀ hnorm x (herr _ hbx)
  have he : (fun y => jointBooleanSampler h c sets (b₀ + L₀ y)) =
      jointAffineBooleanSampler c sets L b := rfl
  rw [he] at ht
  exact ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem canonicalAffineCubeMinorThreshold_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] {h : ℕ} (hh : 0 < h) {c₀ δ η : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < canonicalAffineCubeMinorThreshold O α h c₀ δ η :=
  affineCubeMinorThreshold_pos Unit O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hδ hη

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

omit decidableEqAlpha in
theorem jointAffineBooleanInverseBudget_le [DecidableEq α]
    (h : D → ℕ) (C κ : D → ℝ) (δ : ℝ) (d : D) :
    δ⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 (κ d) ≤
      jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ := by
  classical
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast Finset.single_le_sum (f := fun e => Real.toNNReal
    (δ⁻¹ * productMinorInverseBound (Fintype.card (O e)) (Fintype.card α) (h e) (C e) 1 (κ e)))
    (fun _ _ => zero_le) (Finset.mem_univ d)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem jointAffineBoolean_source_density_comparison
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (η : D → ℝ) (hη : ∀ d, 0 < η d)
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d z, width d z ≠ 0) (hwidth : ∀ d z, δ ≤ |width d z|)
    (hbox : ∀ d z, |center d z| + |width d z| ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) :
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let U := jointAffineBooleanSampler c sets L center
    let f := regularizedImageDensity (jointBooleanSource h) U ρ
    let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
    let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
    let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
    let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)), ContDiff ℝ 2 V →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (K : ℝ) * ε ≤ 1 / 2 →
    (∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ ε) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (V ∘ slice) φ| ≤
        4 * (∑ d, η d) + jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H * ρ +
          4 * (Fintype.card (Σ d, O d) : ℝ) *
            Real.sqrt (jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ * ε) := by
  intro L slice U f r κ K H
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  have hUm : Measurable U := (jointAffineBooleanSampler_contDiff c sets L center).continuous.measurable
  have hp := regularizedImageDensity_probability (jointBooleanSource h) U hUm ρ hρ
  have hb := regularizedImageDensity_bounds (jointBooleanSource h) U hUm ρ hρ
  refine ⟨hb.1, hp.2.1, hp.2.2, hb.2, ?_⟩
  intro V hV ε hε hεone hsmall herr φ hφ hbound
  obtain ⟨sel, hs⟩ := exists_canonical_joint_affine_good_mass_s2 h hh c sets hsets hcard block hblock
    c₀ hc₀ hclow ψ hψ hrange hzero hone
  have hmass := hs δ η hδ hη center width hw hwidth hbox
  have hr (d) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))
  have hκ (d) : 0 < κ d := canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)
  have hL (d) : ‖(L d).toContinuousLinearMap‖ ≤ 1 :=
    coordinateScaleEquiv_norm_le (width d) (hw d) zero_le_one
      (fun z => (le_add_of_nonneg_left (abs_nonneg (center d z))).trans (hbox d z))
  have hLinv (d) : δ * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1 :=
    coordinateScaleEquiv_scaled_inverse_norm_le (width d) (hw d) hδ (hwidth d)
  have hbx (d) (x : BlockParameter (B d) (Fin (h d)) α → ℝ) (hx : ∀ z, |x z| ≤ 1) :
      ∀ z, |(center d + L d x) z| ≤ 1 := coordinateScaleEquiv_affine_box _ _ _ (hbox d) x hx
  have hK := jointAffineBooleanInverseBudget_le (O := O) (α := α) h C κ δ
  have hH := jointBooleanDerivativeBudget_le (B := B) (O := O) (α := α) h C
  have hreg := jointAffineBoolean_regularization_error_s2 c sets block hblock
    (fun d => ⟨0, hh d⟩) sel hcard L center (fun _ => δ) (fun _ => hδ) (fun _ => hδone)
    hL hLinv hbx C hC hcup ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
    hmass ρ hρ φ hφ hbound
  have hsmooth : ContDiff ℝ 2 (V ∘ slice) := hV.comp
    (contDiff_const.add (sigmaAxisOperator (fun d => (L d).toContinuousLinearMap)).contDiff)
  have he := jointAffineBoolean_c2_error_transport c sets L center hL hbx V hV herr
  have hcomp := jointAffineBoolean_good_weight_comparison_s2 c sets block hblock
    (fun d => ⟨0, hh d⟩) sel hcard L center (fun _ => δ) (fun _ => hδ) (fun _ => hδone)
    hL hLinv hbx C hC hcup ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
    (V ∘ slice) hsmooth hε hεone hsmall hmass he φ hφ hbound
  calc
    _ ≤ |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) U φ| +
        |mappedTest (jointBooleanSource h) U φ - mappedTest (jointBooleanSource h) (V ∘ slice) φ| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      have ht := add_le_add hreg hcomp
      dsimp only [jointAffineBooleanErrorBudget]
      linarith only [ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanTolerance
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_uniform_joint_affine_source_tolerance_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)), ContDiff ℝ 2 V →
    (∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ t ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ t ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ t) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (V ∘ slice) φ| ≤ E := by
  let η : D → ℝ := fun _ => E / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hE (by positivity)
  have hmass : 4 * (∑ d, η d) ≤ E / 3 := by
    have hn : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hv : 0 ≤ E / (12 * ((Fintype.card D : ℝ) + 1)) := (div_pos hE (by positivity)).le
    have he : ((Fintype.card D : ℝ) + 1) * (E / (12 * ((Fintype.card D : ℝ) + 1))) = E / 12 := by
      field_simp
    have hm := mul_le_mul_of_nonneg_right (show (Fintype.card D : ℝ) ≤ (Fintype.card D : ℝ) + 1 by linarith) hv
    rw [he] at hm
    simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  have hr : ∀ d i, 0 ≤ r d i := fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le
  have hκ : ∀ d, 0 ≤ κ d := fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le
  have hQ : 0 ≤ Q := by
    have hS := jointBooleanWeightBudget_nonneg (O := O) (α := α) h C hC A T r hr κ hκ
    dsimp only [Q, jointAffineBooleanErrorBudget]
    positivity
  let ρ : ℝ≥0 := ⟨min 1 (E / (3 * (1 + (L : ℝ)))), by positivity⟩
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hE (by positivity))
  have hρone : ρ ≤ 1 := by
    change min (1 : ℝ) (E / (3 * (1 + (L : ℝ)))) ≤ 1
    exact min_le_left _ _
  have hnoise : (L : ℝ) * ρ ≤ E / 3 := by
    have hd : (ρ : ℝ) ≤ E / (3 * (1 + (L : ℝ))) := min_le_right _ _
    have he := (le_div_iff₀ (show 0 < 3 * (1 + (L : ℝ)) by positivity)).mp hd
    nlinarith [ρ.coe_nonneg]
  let t := polynomialPerturbationScale K 1 Q (E / 3) (Fintype.card (Σ d, O d))
  have ht := polynomialPerturbationScale_spec K.coe_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    hQ (show 0 < E / 3 by positivity) (Fintype.card (Σ d, O d))
  have hsmall : (K : ℝ) * t ≤ 1 / 2 := by simpa only [mul_one] using ht.2.2.1
  have hroot : 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * t) ≤ E / 3 := by
    apply le_trans _ ht.2.2.2.2
    gcongr
    nlinarith [ht.1]
  refine ⟨ρ, hρ, hρone, rfl, t, ht.1, ht.2.1, rfl, ?_⟩
  intro c hclow hcup center width hw hwidth hbox
  have hs := jointAffineBoolean_source_density_comparison h hh c sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition δ hδ hδone η hη
    center width hw hwidth hbox ρ hρ
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro V hV herr φ hφ hbound
  have he := hs.2.2.2.2 V hV t ht.1 ht.2.1 hsmall herr φ hφ hbound
  exact he.trans (by change 4 * (∑ d, η d) + (L : ℝ) * ρ +
    4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * t) ≤ E; linarith only [hmass, hnoise, hroot])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointAffinePolynomialSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z : Type*} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_uniform_joint_affine_polynomial_source_with_scales_s2_oai
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Cp δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ p : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ,
    (∀ o i, (p o).degreeOf i ≤ degree) → (∀ o m, |(p o).coeff m| ≤ Cp) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    parameterPolynomialMap p 0 z = jointBooleanSampler h c sets →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) ((parameterPolynomialMap p t z) ∘ slice) φ| ≤ E := by
  obtain ⟨ρ, hρ, hρone, hρeq, ε, hε, hεone, hεeq, hs⟩ := exists_uniform_joint_affine_source_tolerance_with_scales
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition δ hδ hδone hE
  let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _ hCp
  let t := ε / (1 + M)
  have ht : 0 < t := div_pos hε (by positivity)
  have hte : t ≤ ε := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have htone : t ≤ 1 := hte.trans hεone
  have htM : t * M ≤ ε := by
    have he : t * (1 + M) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, ?_, ?_⟩
  · change ε / (1 + M) = _
    rw [hεeq]
    rfl
  intro c hclow hcup center width hw hwidth hbox
  have hd := hs c hclow hcup center width hw hwidth hbox
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  intro p hpdeg hpcoeff z hz hpzero φ hφ hbound
  apply hd.2.2.2.2 (parameterPolynomialMap p t z)
    ((parameterPolynomialMap_contDiff p t z).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)) _ φ hφ hbound
  intro x hx
  have he := parameterPolynomialMap_uniform_c2_error p hpdeg hCp hpcoeff
    (show |t| ≤ 1 by rwa [abs_of_pos ht]) z hz x hx
  rw [hpzero, abs_of_pos ht] at he
  exact ⟨he.1.trans htM, he.2.1.trans htM, he.2.2.trans htM⟩

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.exists_uniform_joint_affine_polynomial_source_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.exists_uniform_joint_affine_polynomial_source_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5}
