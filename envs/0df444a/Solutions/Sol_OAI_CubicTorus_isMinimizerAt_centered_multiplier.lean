-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_centered_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:28.948279+00:00
-- url     : https://prove2.me/submissions/19de46e8-a0fb-4103-9d0a-eb996e6dd0ad

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma admissible_zero : AdmissibleField (fun _ => 0) := by
  exact ⟨contDiff_const, by simp, by simp⟩

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

lemma admissible_neg {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x => -F x) := by
  refine ⟨hF.1.neg, ?_, ?_⟩
  · intro n x
    change -F (x + latticeVector n) = -F x
    rw [hF.2.1 n x]
  · intro x
    simpa using hF.2.2 x

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

lemma abs_flux_le_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ (perimeter E).toReal := by
  apply abs_le.mpr
  constructor
  · have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y => -F y) x) ≤ perimeter E :=
      le_iSup_of_le (fun y => -F y) (le_iSup_of_le (admissible_neg hF) le_rfl)
    simp_rw [divergence_neg, integral_neg] at hh
    have := (ENNReal.ofReal_le_iff_le_toReal hE).mp hh
    linarith
  · exact (ENNReal.ofReal_le_iff_le_toReal hE).mp
      (le_iSup_of_le F (le_iSup_of_le hF le_rfl))

lemma abs_flux_le_mul_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ k * (perimeter E).toReal := by
  have hG : AdmissibleField (fun x => k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      calc
        k⁻¹ * ‖F x‖ ≤ k⁻¹ * k := mul_le_mul_of_nonneg_left (hb x) (by positivity)
        _ = 1 := inv_mul_cancel₀ hk.ne'
  have hg := abs_flux_le_perimeter hE hG
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hk)] at hg
  calc
    _ = k * (k⁻¹ * |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hk.le

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

namespace CubicTorus
open Filter
open scoped Topology

lemma coordinateMove_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateMove i f t) := by
  unfold coordinateMove
  fun_prop

lemma coordinateMove_hasFDerivAt (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (t : ℝ) :
    HasFDerivAt (coordinateMove i f t) (coordinateMoveDeriv i f t point) point := by
  have h₁ : HasFDerivAt (fun y : Cover ↦ y) (ContinuousLinearMap.id ℝ Cover) point :=
    hasFDerivAt_id point
  have h₂ := (hf.hasFDerivAt.const_mul t).smul_const
    (EuclideanSpace.single i (1 : ℝ) : Cover)
  have he : coordinateMoveDeriv i f t point = ContinuousLinearMap.id ℝ Cover +
      (t • fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ) : Cover) := by
    ext y j
    simp [coordinateMoveDeriv, mul_comm]
  rw [he]
  exact h₁.add h₂

lemma coordinateMove_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) (n : Fin 3 → ℤ) (x : Cover) :
    coordinateMove i f t (x + latticeVector n) = coordinateMove i f t x + latticeVector n := by
  simp only [coordinateMove, hp]
  abel

lemma coordinateMove_apply (i j : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    coordinateMove i f t x j = x j + if i = j then t * f x else 0 := by
  by_cases h : i = j <;> simp [coordinateMove, h, eq_comm]

lemma coordinateMoveDeriv_det (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    (coordinateMoveDeriv i f t x).det = coordinateJacobian i f t x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (coordinateMoveDeriv i f t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) +
        (if j = i then t * fderiv ℝ f x (EuclideanSpace.single k 1) else 0)) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (coordinateMoveDeriv i f t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    by_cases h : j = i <;> simp [coordinateMoveDeriv, h, mul_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  rw [Matrix.det_fin_three]
  fin_cases i <;> simp [coordinateJacobian]

lemma coordinateMove_injective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) : Function.Injective (coordinateMove i f t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = -(t * (f x - f y)) • EuclideanSpace.single i 1 := by
    calc
      x - y = coordinateMove i f t x - coordinateMove i f t y -
          (t * (f x - f y)) • EuclideanSpace.single i 1 := by
        unfold coordinateMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖f x - f y‖ := by
    rw [he, norm_smul, norm_neg, Real.norm_eq_abs, abs_mul]
    simp [Real.norm_eq_abs]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    have hz := hLip.norm_sub_le x y
    calc
      ‖x - y‖ = |t| * ‖f x - f y‖ := hn
      _ ≤ |t| * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

lemma linearForm_apply_basis (L : Cover →L[ℝ] ℝ) (v : Cover) :
    L v = ∑ j : Fin 3, v j * L (EuclideanSpace.single j 1) := by
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, map_sum]
  simp

lemma divergence_comp_coordinateMove (i : Fin 3) {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) {G : Cover → Cover} {time : ℝ}
    (hG : DifferentiableAt ℝ G (coordinateMove i f time point)) :
    divergence (fun y ↦ G (coordinateMove i f time y)) point =
      divergence G (coordinateMove i f time point) +
        time * fderiv ℝ f point
          (fderiv ℝ G (coordinateMove i f time point) (EuclideanSpace.single i 1)) := by
  have hm := coordinateMove_hasFDerivAt i hf time
  have hd := (hG.hasFDerivAt.comp point hm).fderiv
  change fderiv ℝ (fun y ↦ G (coordinateMove i f time y)) point = _ at hd
  simp only [divergence, hd,
    coordinateMoveDeriv, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateJacobian_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateJacobian i f t) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  unfold coordinateJacobian
  fun_prop

lemma coordinatePullback_contDiff (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePullback i f t G) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hm := coordinateMove_contDiff i hf t
  have hj := coordinateJacobian_contDiff i hf t
  unfold coordinatePullback
  exact (hj.smul (hG.comp hm)).sub
    ((contDiff_const.mul (hd.clm_apply (hG.comp hm))).smul contDiff_const)

lemma coordinatePullback_periodic (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ n x, G (x + latticeVector n) = G x) (n : Fin 3 → ℤ) (x : Cover) :
    coordinatePullback i f t G (x + latticeVector n) = coordinatePullback i f t G x := by
  simp only [coordinatePullback, coordinateJacobian, fderiv_periodic hp,
    coordinateMove_periodic i hp, hG]

lemma coordinatePullback_divergence (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) {G : Cover → Cover}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (coordinatePullback i f t G) x =
      coordinateJacobian i f t x * divergence G (coordinateMove i f t x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := coordinateMove_hasFDerivAt i hfd t
  have hg := (hG.differentiable (by simp)).differentiableAt (x := coordinateMove i f t x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := ((hdf.hasFDerivAt.clm_apply (hasFDerivAt_const
    (EuclideanSpace.single i (1 : ℝ) : Cover) x)).const_mul t).const_add 1
  have hb := (hdf.hasFDerivAt.clm_apply hu).const_mul t
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top))
    (EuclideanSpace.single i 1) (G (coordinateMove i f t x))
  change divergence (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y) -
    (t * fderiv ℝ f y (G (coordinateMove i f t y))) • EuclideanSpace.single i 1) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (coordinateJacobian i f t) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (coordinateJacobian i f t) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ G (coordinateMove i f t y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ
      (fun y ↦ t * fderiv ℝ f y (G (coordinateMove i f t y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ coordinateJacobian i f t y • G (coordinateMove i f t y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ (t * fderiv ℝ f y (G (coordinateMove i f t y))) •
        (EuclideanSpace.single i 1 : Cover)) x := hB.smul_const _
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU,
    divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_coordinateMove i hfd hg]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, zero_add,
    coordinateMoveDeriv, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero]
  dsimp only [coordinateJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

namespace CubicTorus

lemma coordinateJacobian_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) (x : Cover) :
    ‖coordinateJacobian i f t x‖ ≤ 1 + |t| * M := by
  have hd : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ M := by
    simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  calc
    _ ≤ ‖(1 : ℝ)‖ + ‖t * fderiv ℝ f x (EuclideanSpace.single i 1)‖ := norm_add_le _ _
    _ ≤ 1 + |t| * M := by
      rw [norm_one, norm_mul, Real.norm_eq_abs t]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) 1

lemma coordinateJacobian_pos (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    0 < coordinateJacobian i f t x := by
  have hd : |fderiv ℝ f x (EuclideanSpace.single i 1)| ≤ M := by
    simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (EuclideanSpace.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
  rw [← abs_mul] at hb
  have := (abs_le.1 hb).1
  unfold coordinateJacobian
  linarith

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace CubicTorus

lemma coordinatePullback_norm_le (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    (hG : ∀ x, ‖G x‖ ≤ 1) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ 1 + 2 * |t| * M := by
  have hu := hG (coordinateMove i f t x)
  have hd : ‖fderiv ℝ f x (G (coordinateMove i f t x))‖ ≤ M :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [hM x, norm_nonneg (fderiv ℝ f x)])
  calc
    _ ≤ ‖coordinateJacobian i f t x • G (coordinateMove i f t x)‖ +
        ‖(t * fderiv ℝ f x (G (coordinateMove i f t x))) • EuclideanSpace.single i 1‖ :=
      norm_sub_le _ _
    _ ≤ (1 + |t| * M) + |t| * M := by
      simp only [norm_smul, norm_mul]
      have he : ‖(EuclideanSpace.single i (1 : ℝ) : Cover)‖ = 1 := by simp
      rw [he, mul_one, Real.norm_eq_abs t]
      exact add_le_add
        (by simpa only [mul_one] using
          (mul_le_mul (coordinateJacobian_norm_le i hM t x) hu
            (norm_nonneg _) (by positivity)))
        (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma fiberPoint_self (i : Fin 3) (x : Cover) : fiberPoint i x (x i) = x := by
  simp [fiberPoint]

lemma fiberPoint_apply_same (i : Fin 3) (x : Cover) (u : ℝ) : fiberPoint i x u i = u := by
  simp [fiberPoint]

lemma norm_fiberPoint_sub (i : Fin 3) (x : Cover) (u v : ℝ) :
    ‖fiberPoint i x u - fiberPoint i x v‖ = |u - v| := by
  have he : fiberPoint i x u - fiberPoint i x v =
      (u - v) • EuclideanSpace.single i 1 := by
    unfold fiberPoint
    module
  rw [he, norm_smul]
  simp

lemma coordinateMove_fiber_strictMono (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) (x : Cover) :
    StrictMono (fun u : ℝ ↦ coordinateMove i f t (fiberPoint i x u) i) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro u v huv
  have hb := hLip.norm_sub_le (fiberPoint i x v) (fiberPoint i x u)
  rw [norm_fiberPoint_sub, Real.norm_eq_abs, abs_of_pos (sub_pos.2 huv)] at hb
  have hc := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  rw [← abs_mul] at hc
  have hd := (abs_le.1 hc).1
  simp only [coordinateMove_apply, fiberPoint_apply_same, ↓reduceIte]
  nlinarith [mul_pos (sub_pos.2 ht) (sub_pos.2 huv)]

lemma coordinateMove_mapsTo_cube (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) :
    MapsTo (coordinateMove i f t) fundamentalCube fundamentalCube := by
  intro x hx j
  by_cases hij : i = j
  · subst j
    have hmono := coordinateMove_fiber_strictMono i hf hM ht x
    have hzero : coordinateMove i f t (fiberPoint i x 0) i = 0 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inl (fiberPoint_apply_same i x 0))]
      simp
    have hone : coordinateMove i f t (fiberPoint i x 1) i = 1 := by
      rw [coordinateMove_apply, fiberPoint_apply_same,
        hface _ (Or.inr (fiberPoint_apply_same i x 1))]
      simp
    have hlo := hmono.monotone (hx i).1
    have hhi := hmono (hx i).2
    rw [hzero, fiberPoint_self] at hlo
    dsimp only at hhi
    rw [hone, fiberPoint_self] at hhi
    exact ⟨hlo, hhi⟩
  · simpa [coordinateMove_apply, hij] using hx j

end CubicTorus

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

lemma measurableSet_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (coordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) :=
    continuous_id.add ((continuous_const.mul hf.continuous).smul continuous_const)
  exact (hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)) |>.preimage
      measurable_representative

lemma coordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) (E : Set Torus) :
    fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E) =
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  ext x
  constructor
  · rintro ⟨hx, hE⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E) at hE
    rwa [representative_quotientMap_of_mem hx] at hE
  · intro hx
    have hc : x ∈ fundamentalCube := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact coordinateMove_mapsTo_cube i hf hM hface ht hy.1
    refine ⟨hc, ?_⟩
    change representative (quotientMap x) ∈
      coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E)
    rwa [representative_quotientMap_of_mem hc]

lemma integral_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) (g : Cover → ℝ) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateRegion i f t E), g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        coordinateJacobian i f t x * g (coordinateMove i f t x) := by
  rw [coordinateRegion_lift i hf hM hface ht]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det, abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x), smul_eq_mul]

lemma perimeter_coordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (coordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_coordinateRegion i hfd hM hface ht hE]
  have hh := abs_flux_le_mul_perimeter hP
    (coordinatePullback_contDiff i hf t hG.1) (coordinatePullback_periodic i hp t hG.2.1)
    hC (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  calc
    _ ≤ ENNReal.ofReal ((1 + 2 * |t| * M) * (perimeter E).toReal) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hh)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]
      rfl

lemma finitePerimeter_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (coordinateRegion i f t E) := by
  refine ⟨(measurableSet_coordinateRegion i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

lemma volume_coordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hfd := hf.differentiable (by simp)
  have hi : IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube :=
    integrableOn_periodic_continuous
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun n x ↦ by rw [fderiv_periodic hp])
  have hv := integral_coordinateRegion i hfd hM hface ht hE (fun _ ↦ 1)
  simp only [mul_one, coordinateJacobian] at hv
  rw [integral_add (integrable_const 1) ((hi.mono_set inter_subset_left).const_mul t),
    integral_const_mul] at hv
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hv
  rw [realVolume_lift hE,
    realVolume_lift (measurableSet_coordinateRegion i hfd hM ht hE)]
  exact hv

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma inner_coordinatePullback (i : Fin 3) (f : Cover → ℝ) (t : ℝ)
    (G : Cover → Cover) (x n : Cover) :
    ⟪n, coordinatePullback i f t G x⟫ =
      ⟪coordinateCofactor i f t x n, G (coordinateMove i f t x)⟫ := by
  simp only [coordinatePullback, coordinateCofactor, inner_sub_right, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, inner_gradient_left]
  ring

lemma continuous_coordinateCofactor (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    Continuous (fun z : NormalBundle ↦ coordinateCofactor i f t z.1 z.2) := by
  unfold coordinateCofactor
  exact (((coordinateJacobian_contDiff i hf t).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    ((continuous_const.mul ((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ)
      continuous_const)).smul ((gradient_contDiff hf).continuous.comp
        (continuous_subtype_val.comp continuous_fst)))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinateCofactor_eq (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) :
    coordinateCofactor i f t x n = n + t • coordinateNormalVelocity i f x n := by
  unfold coordinateCofactor coordinateJacobian coordinateNormalVelocity
  module

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

lemma exists_wallVariation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0) :
    ∃ D : WallVariation, D.coordinate = i ∧ D.function = f := by
  obtain ⟨M, hM, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  refine ⟨⟨i, f, ⟨M, hM⟩, hf, hp, ?_, hface⟩, rfl, rfl⟩
  intro x
  exact_mod_cast hbound x

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma coordinatePullback_smul (i : Fin 3) (f : Cover → ℝ) (t c : ℝ)
    (F : Cover → Cover) (x : Cover) :
    coordinatePullback i f t (fun y ↦ c • F y) x = c • coordinatePullback i f t F x := by
  simp only [coordinatePullback, map_smul, smul_sub, smul_smul]
  module

lemma coordinatePullback_norm_le_mul (i : Fin 3) {f : Cover → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (t : ℝ) {G : Cover → Cover}
    {k : ℝ} (hk : 0 < k) (hG : ∀ x, ‖G x‖ ≤ k) (x : Cover) :
    ‖coordinatePullback i f t G x‖ ≤ (1 + 2 * |t| * M) * k := by
  have hnorm : ∀ y, ‖k⁻¹ • G y‖ ≤ 1 := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
    exact (mul_le_mul_of_nonneg_left (hG y) (inv_nonneg.mpr hk.le)).trans_eq
      (inv_mul_cancel₀ hk.ne')
  have hh := coordinatePullback_norm_le i hM0 hM t hnorm x
  rw [coordinatePullback_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hk.le)] at hh
  calc
    _ = k * (k⁻¹ * ‖coordinatePullback i f t G x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ k * (1 + 2 * |t| * M) := mul_le_mul_of_nonneg_left hh hk.le
    _ = _ := mul_comm _ _

lemma continuous_doubleCofactor (a b : WallVariation) (t s : ℝ) :
    Continuous (fun z : NormalBundle ↦ doubleCofactor a b t s z.1 z.2) := by
  have hc := (coordinateMove_contDiff a.coordinate a.smooth t).continuous.comp
    (continuous_subtype_val.comp continuous_fst : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)))
  have hn := continuous_coordinateCofactor a.coordinate a.smooth t
  unfold doubleCofactor coordinateCofactor
  exact (((coordinateJacobian_contDiff b.coordinate b.smooth s).continuous.comp hc).smul hn).sub
    ((continuous_const.mul (hn.inner (𝕜 := ℝ) continuous_const)).smul
      ((gradient_contDiff b.smooth).continuous.comp hc))

theorem perimeter_doubleRegion_le_normalArea (a b : WallVariation) {t s : ℝ}
    (ht : |t| * (a.bound : ℝ) < 1) (hs : |s| * (b.bound : ℝ) < 1)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) :
    perimeter (doubleRegion a b t s E) ≤ ENNReal.ofReal
      (∫ z, ‖doubleCofactor a b t s z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  have hEa := measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
    a.derivative_bound ht hE
  have haM : ∀ x, ‖fderiv ℝ a.function x‖ ≤ (a.bound : ℝ) := fun x ↦ by
    exact_mod_cast a.derivative_bound x
  have hbM : ∀ x, ‖fderiv ℝ b.function x‖ ≤ (b.bound : ℝ) := fun x ↦ by
    exact_mod_cast b.derivative_bound x
  have hak : 0 < 1 + 2 * |t| * (a.bound : ℝ) := by positivity
  have hbk : 0 < 1 + 2 * |s| * (b.bound : ℝ) := by positivity
  unfold perimeter doubleRegion
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  let G := coordinatePullback b.coordinate b.function s F
  have hG := coordinatePullback_contDiff b.coordinate b.smooth s hF.1
  have hGp := coordinatePullback_periodic b.coordinate b.periodic s hF.2.1
  have hΓ := coordinatePullback_contDiff a.coordinate a.smooth t hG
  rw [integral_coordinateRegion b.coordinate (b.smooth.differentiable (by simp))
    b.derivative_bound b.faces hs hEa]
  simp_rw [← coordinatePullback_divergence b.coordinate b.smooth s hF.1]
  rw [integral_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
    a.derivative_bound a.faces ht hE]
  have hflux := normalMeasure_flux hμ hΓ
    (coordinatePullback_periodic a.coordinate a.periodic t hGp) (mul_pos hak hbk)
    (coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg haM t hbk
      (coordinatePullback_norm_le b.coordinate b.bound.coe_nonneg hbM s hF.2.2))
  simp_rw [coordinatePullback_divergence a.coordinate a.smooth t hG] at hflux
  change ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    coordinateJacobian a.coordinate a.function t x *
      divergence G (coordinateMove a.coordinate a.function t x)) ≤ _
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_doubleCofactor a b t s).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover), coordinatePullback a.coordinate a.function t G z.1⟫ ≤ _
    rw [inner_coordinatePullback]
    dsimp only [G]
    rw [inner_coordinatePullback]
    exact (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma directionalDeriv_norm_le (a : WallVariation) (x : Cover) :
    ‖fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1)‖ ≤ (a.bound : ℝ) := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ a.function x)
    (EuclideanSpace.single a.coordinate 1)
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (by exact_mod_cast a.derivative_bound x)

lemma gradient_norm_le (a : WallVariation) (x : Cover) :
    ‖gradient a.function x‖ ≤ (a.bound : ℝ) := by
  have h : ‖fderiv ℝ a.function x‖ ≤ (a.bound : ℝ) := by
    exact_mod_cast a.derivative_bound x
  simpa only [gradient, LinearIsometryEquiv.norm_map] using h

lemma coordinateNormalVelocity_norm_le (a : WallVariation) (x n : Cover) :
    ‖coordinateNormalVelocity a.coordinate a.function x n‖ ≤ 2 * (a.bound : ℝ) * ‖n‖ := by
  have hi : ‖⟪n, EuclideanSpace.single a.coordinate (1 : ℝ)⟫‖ ≤ ‖n‖ := by
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      abs_real_inner_le_norm n (EuclideanSpace.single a.coordinate (1 : ℝ) : Cover)
  unfold coordinateNormalVelocity
  calc
    _ ≤ ‖fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1) • n‖ +
        ‖⟪n, EuclideanSpace.single a.coordinate 1⟫ • gradient a.function x‖ := norm_sub_le _ _
    _ ≤ (a.bound : ℝ) * ‖n‖ + ‖n‖ * (a.bound : ℝ) := by
      simp only [norm_smul]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (directionalDeriv_norm_le a x) (norm_nonneg _))
        (mul_le_mul hi (gradient_norm_le a x) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

lemma transportedFlux_zero (a b : WallVariation) (E : Set Torus) :
    transportedFlux a b E 0 = directionalFlux E b.coordinate b.function := by
  simp only [transportedFlux, coordinateJacobian, zero_mul, add_zero, one_mul,
    coordinateMove, zero_smul, directionalFlux]

lemma continuousAt_transportedFlux (a b : WallVariation) (E : Set Torus) :
    ContinuousAt (transportedFlux a b E) 0 := by
  have hg : Continuous (fun x ↦ fderiv ℝ b.function x (EuclideanSpace.single b.coordinate 1)) :=
    (b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmeas (t : ℝ) : Continuous (fun x ↦
      coordinateJacobian a.coordinate a.function t x *
        fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
          (EuclideanSpace.single b.coordinate 1)) :=
    (coordinateJacobian_contDiff a.coordinate a.smooth t).continuous.mul
      (hg.comp (coordinateMove_contDiff a.coordinate a.smooth t).continuous)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
    (continuous_abs.continuousAt.eventually (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1))).mono
      fun _ h ↦ h.le
  have hbound : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : Cover,
      ‖coordinateJacobian a.coordinate a.function t x *
        fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
          (EuclideanSpace.single b.coordinate 1)‖ ≤ (1 + (a.bound : ℝ)) * b.bound := by
    filter_upwards [hsmall] with t ht x
    rw [norm_mul]
    apply mul_le_mul _ (directionalDeriv_norm_le b _) (norm_nonneg _) (by positivity)
    exact (coordinateJacobian_norm_le a.coordinate (M := (a.bound : ℝ)) (fun y ↦ by
      exact_mod_cast a.derivative_bound y) t x).trans (by
        simpa only [one_mul] using add_le_add (le_refl (1 : ℝ))
          (mul_le_mul_of_nonneg_right ht a.bound.coe_nonneg))
  unfold transportedFlux
  apply continuousAt_of_dominated (bound := fun _ ↦ (1 + (a.bound : ℝ)) * b.bound)
    (Eventually.of_forall fun t ↦ (hmeas t).aestronglyMeasurable)
    (hbound.mono fun t ht ↦ Eventually.of_forall ht) (integrable_const _) ?_
  apply Eventually.of_forall
  intro x
  have hc : Continuous (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) := by
    exact continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  exact (((continuous_const.add (continuous_id.mul continuous_const)) :
    Continuous (fun t : ℝ ↦ coordinateJacobian a.coordinate a.function t x)).mul
    (hg.comp hc)).continuousAt

lemma volume_doubleRegion (a b : WallVariation) {t s : ℝ}
    (ht : |t| * (a.bound : ℝ) < 1) (hs : |s| * (b.bound : ℝ) < 1)
    {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real (doubleRegion a b t s E) = torusVolume.real E +
      t * directionalFlux E a.coordinate a.function + s * transportedFlux a b E t := by
  unfold doubleRegion
  rw [volume_coordinateRegion b.coordinate b.smooth b.periodic b.derivative_bound b.faces hs
    (measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
      a.derivative_bound ht hE)]
  rw [volume_coordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound a.faces ht hE,
    integral_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
      a.derivative_bound a.faces ht hE]
  rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_coordinateNormalVelocity_pair (a : WallVariation) :
    Continuous (fun p : Cover × Cover ↦
      coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact ((((a.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    continuous_fst).smul continuous_snd).sub
    ((continuous_snd.inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff a.smooth).continuous.comp continuous_fst))

lemma doubleCofactor_eq (a b : WallVariation) (k t : ℝ) (x n : Cover) :
    doubleCofactor a b t (t * k) x n = n + t • doubleVelocityCoefficient a b k t x n := by
  simp only [doubleCofactor, coordinateCofactor_eq, doubleVelocityCoefficient]
  module

lemma continuous_doubleVelocityCoefficient (a b : WallVariation) (k t : ℝ) :
    Continuous (fun z : NormalBundle ↦ doubleVelocityCoefficient a b k t z.1 z.2) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hn := continuous_normalUnit
  have hA := continuous_coordinateNormalVelocity a.coordinate a.smooth
  have hm := (coordinateMove_contDiff a.coordinate a.smooth t).continuous.comp hx
  unfold doubleVelocityCoefficient
  have ht : Continuous (fun _ : NormalBundle ↦ t) := continuous_const
  have hk : Continuous (fun _ : NormalBundle ↦ k) := continuous_const
  convert hA.add (hk.smul ((continuous_coordinateNormalVelocity_pair b).comp
      (hm.prodMk (hn.add (ht.smul hA))))) using 1
  all_goals try with_reducible_and_instances rfl
  ext z j
  rfl

lemma continuous_velocityAlong (a b : WallVariation) (x n : Cover) :
    Continuous (fun t : ℝ ↦ coordinateNormalVelocity b.coordinate b.function
      (coordinateMove a.coordinate a.function t x)
      (n + t • coordinateNormalVelocity a.coordinate a.function x n)) := by
  have hm : Continuous (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hn : Continuous (fun t : ℝ ↦ n + t • coordinateNormalVelocity a.coordinate a.function x n) :=
    continuous_const.add (continuous_id.smul continuous_const)
  simpa! only [Function.comp_def] using
    (continuous_coordinateNormalVelocity_pair b).comp (hm.prodMk hn)

lemma continuousAt_doubleVelocityCoefficient (a b : WallVariation) {k : ℝ → ℝ}
    (hk : ContinuousAt k 0) (x n : Cover) :
    ContinuousAt (fun t ↦ doubleVelocityCoefficient a b (k t) t x n) 0 := by
  exact continuousAt_const.add (hk.smul (continuous_velocityAlong a b x n).continuousAt)

lemma doubleVelocityCoefficient_norm_le (a b : WallVariation) {k t K : ℝ}
    (ht : |t| ≤ 1) (hk : |k| ≤ K) (x : Cover) {n : Cover} (hn : ‖n‖ = 1) :
    ‖doubleVelocityCoefficient a b k t x n‖ ≤
      2 * (a.bound : ℝ) + K * (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ))) := by
  have hK : 0 ≤ K := (abs_nonneg k).trans hk
  have hA : ‖coordinateNormalVelocity a.coordinate a.function x n‖ ≤ 2 * (a.bound : ℝ) := by
    simpa only [hn, mul_one] using coordinateNormalVelocity_norm_le a x n
  have hn' : ‖n + t • coordinateNormalVelocity a.coordinate a.function x n‖ ≤
      1 + 2 * (a.bound : ℝ) := by
    calc
      _ ≤ ‖n‖ + ‖t • coordinateNormalVelocity a.coordinate a.function x n‖ := norm_add_le _ _
      _ ≤ 1 + 1 * (2 * (a.bound : ℝ)) := by
        rw [hn, norm_smul, Real.norm_eq_abs]
        exact add_le_add (le_refl (1 : ℝ))
          (mul_le_mul ht hA (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hB := (coordinateNormalVelocity_norm_le b
    (coordinateMove a.coordinate a.function t x)
    (n + t • coordinateNormalVelocity a.coordinate a.function x n)).trans
    (mul_le_mul_of_nonneg_left hn' (by positivity))
  unfold doubleVelocityCoefficient
  calc
    _ ≤ ‖coordinateNormalVelocity a.coordinate a.function x n‖ +
      ‖k • coordinateNormalVelocity b.coordinate b.function
        (coordinateMove a.coordinate a.function t x)
        (n + t • coordinateNormalVelocity a.coordinate a.function x n)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hA (mul_le_mul hk hB (norm_nonneg _) hK)

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma hasDerivAt_smul_continuous_zero {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {b : ℝ → H} (hb : ContinuousAt b 0) :
    HasDerivAt (fun t : ℝ ↦ t • b t) (b 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hb.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  simp [slope_def_module, ht0]

lemma hasDerivAt_norm_unit_perturbation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : H} (hn : ‖n‖ = 1) {b : ℝ → H}
    (hb : ContinuousAt b 0) :
    HasDerivAt (fun t : ℝ ↦ ‖n + t • b t‖) ⟪n, b 0⟫ 0 := by
  have hh := (hasDerivAt_smul_continuous_zero hb).const_add n
  have hs := hh.norm_sq.sqrt (by simp [hn])
  simpa only [zero_smul, add_zero, hn, one_pow, Real.sqrt_one, mul_one,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0),
    Real.sqrt_sq (norm_nonneg _)] using hs

lemma norm_slope_unit_perturbation_le {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (n : H) (b : ℝ → H) (t : ℝ) :
    ‖slope (fun u : ℝ ↦ ‖n + u • b u‖) 0 t‖ ≤ ‖b t‖ := by
  by_cases ht : t = 0
  · simp [ht]
  simp only [slope_def_module, sub_zero, zero_smul, add_zero, norm_smul]
  calc
    ‖t⁻¹‖ * ‖‖n + t • b t‖ - ‖n‖‖ ≤ ‖t⁻¹‖ * ‖(n + t • b t) - n‖ :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
        (abs_norm_sub_norm_le (n + t • b t) n)) (norm_nonneg _)
    _ = ‖b t‖ := by
      rw [add_sub_cancel_left, norm_smul, norm_inv, ← mul_assoc,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]

lemma hasDerivAt_integral_norm_perturbation {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {μ : Measure α}
    (n : α → H) (b : ℝ → α → H) (hn : ∀ z, ‖n z‖ = 1)
    (hint : ∀ t : ℝ, Integrable (fun z ↦ ‖n z + t • b t z‖) μ)
    (hcont : ∀ᵐ z ∂μ, ContinuousAt (fun t ↦ b t z) 0)
    (C : α → ℝ) (hC : Integrable C μ)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ z ∂μ, ‖b t z‖ ≤ C z) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖n z + t • b t z‖ ∂μ)
      (∫ z, ⟪n z, b 0 z⟫ ∂μ) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun z ↦ slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t) μ := by
    intro t
    simp only [slope_def_module, sub_zero]
    exact ((hint t).aestronglyMeasurable.sub (hint 0).aestronglyMeasurable).const_smul (t⁻¹ : ℝ)
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ z ∂μ,
      ‖slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t‖ ≤ C z := by
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with t ht
    exact ht.mono fun z hz ↦ (norm_slope_unit_perturbation_le (n z) (fun u ↦ b u z) t).trans hz
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun t : ℝ ↦ slope (fun u : ℝ ↦ ‖n z + u • b u z‖) 0 t)
      (𝓝[≠] 0) (𝓝 ⟪n z, b 0 z⟫) := by
    filter_upwards [hcont] with z hz
    exact (hasDerivAt_norm_unit_perturbation (hn z) hz).tendsto_slope
  have h := tendsto_integral_filter_of_dominated_convergence C
    (Eventually.of_forall hmeas) hb hC hlim
  apply h.congr'
  filter_upwards [] with t
  simp only [slope_def_module, sub_zero, integral_smul, integral_sub (hint t) (hint 0)]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrable_normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : WallVariation) :
    Integrable (fun z : NormalBundle ↦
      ⟪(z.2 : Cover), coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫)
        (μ : Measure NormalBundle) :=
  (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity a.coordinate a.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integral_inner_doubleVelocity_zero (μ : FiniteMeasure NormalBundle)
    (a b : WallVariation) (k : ℝ) :
    (∫ z, ⟪(z.2 : Cover), doubleVelocityCoefficient a b k 0 z.1 z.2⟫
      ∂(μ : Measure NormalBundle)) = normalFirstVariation μ a + k * normalFirstVariation μ b := by
  simp only [doubleVelocityCoefficient, coordinateMove, zero_mul, zero_smul, add_zero,
    inner_add_right, real_inner_smul_right]
  rw [integral_add (integrable_normalFirstVariation μ a)
    ((integrable_normalFirstVariation μ b).const_mul k), integral_const_mul]
  rfl

lemma integrable_doublePerturbation (a b : WallVariation) (μ : FiniteMeasure NormalBundle)
    (k t : ℝ) :
    Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover) +
      t • doubleVelocityCoefficient a b k t z.1 z.2‖) (μ : Measure NormalBundle) := by
  have hc : Continuous (fun z : NormalBundle ↦ (z.2 : Cover) +
      t • doubleVelocityCoefficient a b k t z.1 z.2) :=
    continuous_normalUnit.add
      ((continuous_const : Continuous (fun _ : NormalBundle ↦ t)).smul
        (continuous_doubleVelocityCoefficient a b k t))
  exact hc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma doubleVelocityCoefficient_eventually_bounded (a b : WallVariation)
    {k : ℝ → ℝ} (hk : ContinuousAt k 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ z : NormalBundle,
      ‖doubleVelocityCoefficient a b (k t) t z.1 z.2‖ ≤
      2 * (a.bound : ℝ) + (|k 0| + 1) *
      (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ))) := by
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |k t| ≤ |k 0| + 1 :=
    (hk.abs.eventually (eventually_lt_nhds (by linarith : |k 0| < |k 0| + 1))).mono
      fun _ h ↦ h.le
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
    (continuous_abs.continuousAt.eventually
      (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1))).mono fun _ h ↦ h.le
  filter_upwards [ht, hb] with t ht hb z
  exact doubleVelocityCoefficient_norm_le a b ht hb _ z.2.property

theorem hasDerivAt_doubleNormalArea (a b : WallVariation) (μ : FiniteMeasure NormalBundle)
    {k : ℝ → ℝ} (hk : ContinuousAt k 0) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖doubleCofactor a b t (t * k t) z.1 z.2‖
      ∂(μ : Measure NormalBundle))
      (normalFirstVariation μ a + k 0 * normalFirstVariation μ b) 0 := by
  simp_rw [doubleCofactor_eq]
  rw [← integral_inner_doubleVelocity_zero]
  exact hasDerivAt_integral_norm_perturbation
    (fun z : NormalBundle ↦ (z.2 : Cover))
    (fun t z ↦ doubleVelocityCoefficient a b (k t) t z.1 z.2)
    (fun z ↦ z.2.property) (fun t ↦ integrable_doublePerturbation a b μ (k t) t)
    (Eventually.of_forall fun z ↦ continuousAt_doubleVelocityCoefficient a b hk _ _)
    (fun _ ↦ 2 * (a.bound : ℝ) + (|k 0| + 1) *
      (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ)))) (integrable_const _)
    ((doubleVelocityCoefficient_eventually_bounded a b hk).mono
      fun _ ht ↦ Eventually.of_forall ht)

lemma doubleNormalArea_zero (a b : WallVariation) (μ : FiniteMeasure NormalBundle) :
    (∫ z, ‖doubleCofactor a b 0 0 z.1 z.2‖ ∂(μ : Measure NormalBundle)) = (μ.mass : ℝ) := by
  simp_rw [doubleCofactor, coordinateCofactor_eq, zero_smul, add_zero,
    fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const, smul_eq_mul, mul_one]
  rfl

lemma continuousAt_volumeCorrectionCoefficient (a b : WallVariation) (E : Set Torus)
    (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ContinuousAt (volumeCorrectionCoefficient a b E) 0 := by
  apply continuousAt_const.div (continuousAt_transportedFlux a b E)
  rwa [transportedFlux_zero]

lemma volume_doubleRegion_corrected (a b : WallVariation) {E : Set Torus}
    (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      |t| * (a.bound : ℝ) < 1 ∧
      |t * volumeCorrectionCoefficient a b E t| * (b.bound : ℝ) < 1 ∧
      torusVolume (doubleRegion a b t (t * volumeCorrectionCoefficient a b E t) E) = torusVolume E := by
  have hc := continuousAt_volumeCorrectionCoefficient a b E hB
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| * (a.bound : ℝ) < 1 :=
    (continuous_abs.mul continuous_const).continuousAt.eventually
      (eventually_lt_nhds (by simp : |(0 : ℝ)| * (a.bound : ℝ) < 1))
  have hs : ∀ᶠ t : ℝ in 𝓝 0,
      |t * volumeCorrectionCoefficient a b E t| * (b.bound : ℝ) < 1 :=
    ((continuousAt_id.mul hc).abs.mul continuousAt_const).eventually
      (eventually_lt_nhds (by simp : |(0 : ℝ) * volumeCorrectionCoefficient a b E 0| *
        (b.bound : ℝ) < 1))
  have hn : ∀ᶠ t : ℝ in 𝓝 0, transportedFlux a b E t ≠ 0 :=
    (continuousAt_transportedFlux a b E).eventually_ne (by rwa [transportedFlux_zero])
  filter_upwards [ht, hs, hn] with t ht hs hn
  refine ⟨ht, hs, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change torusVolume.real _ = torusVolume.real E
  rw [volume_doubleRegion a b ht hs hE]
  unfold volumeCorrectionCoefficient
  field_simp [hn]
  ring

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

theorem isMinimizerAt_mixed_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a b : WallVariation) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    normalFirstVariation μ a * directionalFlux E b.coordinate b.function =
      normalFirstVariation μ b * directionalFlux E a.coordinate a.function := by
  let k := volumeCorrectionCoefficient a b E
  have hlocal : IsLocalMin (fun t : ℝ ↦ ∫ z,
      ‖doubleCofactor a b t (t * k t) z.1 z.2‖ ∂(μ : Measure NormalBundle)) 0 := by
    filter_upwards [volume_doubleRegion_corrected a b hE hB] with t ht
    simp only [zero_mul, doubleNormalArea_zero, hμ.1]
    have hEa := measurableSet_coordinateRegion a.coordinate
      (a.smooth.differentiable (by simp)) a.derivative_bound ht.1 hE
    have hfa := finitePerimeter_coordinateRegion a.coordinate a.smooth a.periodic
      a.derivative_bound a.faces ht.1 hE hmin.1.2.ne
    have hfin := finitePerimeter_coordinateRegion b.coordinate b.smooth b.periodic
      b.derivative_bound b.faces ht.2.1 hEa hfa.2.ne
    have hleast := hmin.2.2 _ hfin (ht.2.2.trans hmin.2.1)
    have harea := perimeter_doubleRegion_le_normalArea a b ht.1 ht.2.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] using hh
  have hz := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_doubleNormalArea a b μ (continuousAt_volumeCorrectionCoefficient a b E hB))
  dsimp only [k, volumeCorrectionCoefficient] at hz
  rw [transportedFlux_zero] at hz
  field_simp at hz
  nlinarith

theorem isMinimizerAt_exists_coordinate_multiplier {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (b : WallVariation) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ∃ H : ℝ, ∀ a : WallVariation,
      normalFirstVariation μ a = H * directionalFlux E a.coordinate a.function := by
  refine ⟨normalFirstVariation μ b / directionalFlux E b.coordinate b.function, fun a ↦ ?_⟩
  have h := isMinimizerAt_mixed_stationary hmin hE hμ a b hB
  apply (mul_right_cancel₀ hB)
  calc
    normalFirstVariation μ a * directionalFlux E b.coordinate b.function =
        normalFirstVariation μ b * directionalFlux E a.coordinate a.function := h
    _ = _ := by field_simp

end CubicTorus

namespace CubicTorus

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

lemma wallCutoff_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (wallCutoff i) := by
  unfold wallCutoff
  fun_prop

lemma wallCutoff_periodic (i : Fin 3) (n : Fin 3 → ℤ) (x : Cover) :
    wallCutoff i (x + latticeVector n) = wallCutoff i x := by
  have he : 2 * Real.pi * (x + latticeVector n) i =
      2 * Real.pi * x i + (n i : ℝ) * (2 * Real.pi) := by
    simp only [PiLp.add_apply, latticeVector]
    ring
  simp only [wallCutoff, he, Real.cos_add_int_mul_two_pi]

lemma wallCutoff_face (i : Fin 3) (x : Cover) (hx : x i = 0 ∨ x i = 1) :
    wallCutoff i x = 0 := by
  rcases hx with hx | hx <;> simp [wallCutoff, hx, Real.cos_two_pi]

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalTest_le_one {F : Cover → Cover} (hF : AdmissibleField F) (z : NormalBundle) :
    normalTest F hF.1.continuous z ≤ 1 := by
  calc
    _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [z.2.property, one_mul] using hF.2.2 z.1

theorem normalMeasure_weighted_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (w : C(NormalBundle, ℝ))
    {A : ℝ} (hA : ∀ (F : Cover → Cover) (hF : AdmissibleField F),
      (∫ z, w z * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ A) :
    (∫ z, w z ∂(μ : Measure NormalBundle)) ≤ A := by
  let C : ℝ := ‖w‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hwC (z : NormalBundle) : w z ≤ C := by
    exact (le_abs_self _).trans ((w.norm_coe_le_norm z).trans (by dsimp [C]; linarith))
  let P : ℝ := (perimeter E).toReal
  let I : ℝ := ∫ z, w z ∂(μ : Measure NormalBundle)
  let B : ℝ := P + (A - I) / C
  have hiw : Integrable w (μ : Measure NormalBundle) := w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (F : Cover → Cover) (hF : AdmissibleField F) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) ≤ B := by
    let T := normalTest F hF.1.continuous
    have hiT : Integrable T (μ : Measure NormalBundle) := T.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiwT : Integrable (fun z ↦ w z * T z) (μ : Measure NormalBundle) :=
      (w.continuous.mul T.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hdef (z : NormalBundle) :
        w z - w z * T z ≤ C * (1 - T z) := by
      have hT : 0 ≤ 1 - T z := sub_nonneg.mpr (normalTest_le_one hF z)
      nlinarith [mul_le_mul_of_nonneg_right (hwC z) hT]
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) hdef
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT, integral_const_mul,
      integral_sub (integrable_const (1 : ℝ)) hiT] at hh
    have hmass : (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = P := by
      simpa only [integral_const, smul_eq_mul, mul_one, P,
        FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hμ.1
    rw [hmass] at hh
    have hcap : (∫ z, w z * T z ∂(μ : Measure NormalBundle)) ≤ A := hA F hF
    have hflux : (∫ z, T z ∂(μ : Measure NormalBundle)) =
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := hμ.2 F hF
    rw [← hflux]
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul, div_mul_cancel₀ _ hC.ne']
    dsimp only [I] at *
    nlinarith
  have hB : 0 ≤ B := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hP : perimeter E ≤ ENNReal.ofReal B := by
    unfold perimeter
    exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hbound F hF)
  have hPB : P ≤ B := by
    simpa only [P, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
  have hneg : (A - I) / C ≥ 0 := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hneg hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_weighted_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y ↦ w y • F y) x := by
  obtain ⟨M, hM, hb⟩ := periodic_bounded hw.continuous hp
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x • F x) := hw.smul hF.1
  have hGp : ∀ n x, w (x + latticeVector n) • F (x + latticeVector n) = w x • F x := by
    intro n x
    rw [hp, hF.2.1]
  have hGb (x : Cover) : ‖w x • F x‖ ≤ M + 1 := by
    rw [norm_smul]
    calc
      _ ≤ ‖w x‖ * 1 := mul_le_mul_of_nonneg_left (hF.2.2 x) (norm_nonneg _)
      _ ≤ M + 1 := by simpa only [mul_one] using (hb x).trans (by linarith)
  simpa only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right] using
    normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1) hGb

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

lemma volumeSupport_eq_closure {E : Set Torus} (hE : IsOpen E) :
    volumeSupport E = closure E := by
  apply Subset.antisymm
  · exact Measure.support_restrict_subset.trans inter_subset_left
  · apply closure_minimal _ (isClosed_volumeSupport E)
    have hh := Measure.interior_inter_support (μ := torusVolume) (s := E)
    change E ⊆ (torusVolume.restrict E).support
    simpa only [hE.interior_eq, Measure.support_eq_univ, inter_univ] using hh

lemma isMinimizerAt_closure_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E) = volumeSupport E := by
  rw [← volumeSupport_eq_closure (isOpen_openRepresentative E)]
  exact volumeSupport_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)

lemma isMinimizerAt_frontier_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative E) = volumeSupport E ∩ volumeSupport Eᶜ := by
  rw [frontier, (isOpen_openRepresentative E).interior_eq,
    isMinimizerAt_closure_openRepresentative hV hE hmin]
  simp only [openRepresentative, sdiff_eq, compl_compl]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma norm_quotientMap_le (x : Cover) : ‖quotientMap x‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) QuotientAddGroup.norm_mk_le_norm 2

lemma quotientMap_shortestLift (x : Torus) : quotientMap (shortestLift x) = x := by
  simp only [shortestLift, quotientMap_sub, quotientMap_representative, add_sub_cancel_right]

lemma norm_shortestLift (x : Torus) : ‖shortestLift x‖ = ‖x‖ := by
  have hh := dist_representative_cubeCenter (x + quotientMap cubeCenter)
  simpa only [dist_eq_norm, add_sub_cancel_right, shortestLift] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurableSet_cellBall (a : Cover) (r : ℝ) :
    MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
  Metric.isOpen_ball.measurableSet.preimage (measurable_subtype_coe.comp measurable_fst)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_injective_open_closed_cell {x y : Cover}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (he : quotientMap x = quotientMap y) : x = y := by
  obtain ⟨n, hn⟩ := same_quotient_lattice he
  have hz (i : Fin 3) : n i = 0 := by
    have he' := congrArg (fun z : Cover ↦ z i) hn
    change x i = y i + (n i : ℝ) at he'
    have hlt : (n i : ℝ) < 1 := by linarith [(hx i).2, (hy i).1]
    have hgt : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).1, (hy i).2]
    have hlt' : n i < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n i := by exact_mod_cast hgt
    omega
  rw [show n = 0 from funext hz, latticeVector_zero, add_zero] at hn
  exact hn

lemma quotientMap_image_ball (a : Cover) (r : ℝ) :
    quotientMap '' Metric.ball a r = Metric.ball (quotientMap a) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist (quotientMap y) (quotientMap a) < r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  · intro hx
    refine ⟨shortestLift (x - quotientMap a) + a, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_shortestLift] using hx
    · rw [quotientMap_add, quotientMap_shortestLift, sub_add_cancel]

lemma compactCell_mem_quotient_ball_iff (z : CompactCell) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    quotientMap z ∈ Metric.ball (quotientMap a) r ↔ (z : Cover) ∈ Metric.ball a r := by
  constructor
  · intro hz
    rw [← quotientMap_image_ball a r] at hz
    obtain ⟨y, hy, he⟩ := hz
    have he' := quotientMap_injective_open_closed_cell (compactCell_coordinates z) (hc hy) he.symm
    rwa [he']
  · intro hz
    rw [← quotientMap_image_ball a r]
    exact ⟨z, hz, rfl⟩

lemma cellBallMass_eq_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    cellBallMass μ a r = (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) := by
  unfold cellBallMass
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle) (Metric.ball (quotientMap a) r)).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext z
  exact (compactCell_mem_quotient_ball_iff z.1 a r hc).symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma cubeCenter_closedBall_interior {r : ℝ} (hr : r < 1/2) :
    Metric.closedBall cubeCenter r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-cubeCenter) i).trans
    (show ‖x-cubeCenter‖ ≤ r by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  simp only [PiLp.sub_apply,cubeCenter,Real.norm_eq_abs] at hh
  have ha := abs_le.mp hh
  constructor <;> linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma interiorWallWeight_smooth : ContDiff ℝ (⊤ : ℕ∞) interiorWallWeight := by
  unfold interiorWallWeight
  apply contDiff_prod
  intro i hi
  exact wallCutoff_contDiff i

lemma interiorWallWeight_nonneg (x : Cover) : 0 ≤ interiorWallWeight x := by
  apply Finset.prod_nonneg
  intro i hi
  dsimp [wallCutoff]
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by norm_num)

lemma interiorWallWeight_periodic (n : Fin 3 → ℤ) (x : Cover) :
    interiorWallWeight (x+latticeVector n) = interiorWallWeight x := by
  simp only [interiorWallWeight,wallCutoff_periodic]

lemma interiorWallWeight_face (i : Fin 3) (x : Cover) (hx : x i = 0 ∨ x i = 1) :
    interiorWallWeight x = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (wallCutoff_face i x hx)

lemma interiorWallWeight_center : interiorWallWeight cubeCenter = 1 := by
  have hi (i : Fin 3) : wallCutoff i cubeCenter = 1 := by
    dsimp [wallCutoff,cubeCenter]
    rw [show 2*Real.pi*(1/2) = Real.pi by ring, Real.cos_pi]
    norm_num
  simp [interiorWallWeight,hi]

theorem isMinimizerAt_exists_interior_positive_flux {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ D : WallVariation, 0 < directionalFlux E D.coordinate D.function := by
  obtain ⟨R,c,hR,hcpos,hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  have hc' := hc
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at hc'
  have hwnear : ∀ᶠ x in 𝓝 cubeCenter, (1:ℝ)/2 < interiorWallWeight x :=
    (interiorWallWeight_smooth.continuous.continuousAt.tendsto).eventually
      (Ioi_mem_nhds (by rw [interiorWallWeight_center]; norm_num))
  obtain ⟨s,hs,hsw⟩ := Metric.eventually_nhds_iff.mp hwnear
  let r := min (min s R) (1/4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r ≤ s := (min_le_left _ _).trans (min_le_left _ _)
  have hrR : r ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hr4 : r ≤ 1/4 := min_le_right _ _
  let W : C(NormalBundle,ℝ) := ⟨fun z ↦ interiorWallWeight z.1,
    interiorWallWeight_smooth.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hi : Integrable W (μ : Measure NormalBundle) := W.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hIpos : 0 < ∫ z, W z ∂(μ : Measure NormalBundle) := by
    let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball cubeCenter r}
    have hm : 0 < (μ : Measure NormalBundle).real S := by
      change 0 < cellBallMass μ cubeCenter r
      rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter r
        (Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior (by linarith)))]
      exact (mul_pos hcpos (sq_pos_of_pos hr)).trans_le (hl μ hμ _ hc' r hr hrR)
    have hlow : (μ : Measure NormalBundle).real S*(1/2) ≤ ∫ z in S, W z ∂(μ : Measure NormalBundle) := by
      calc
        _ = ∫ _ in S, (1/2:ℝ) ∂(μ : Measure NormalBundle) := by simp
        _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn
          (measurableSet_cellBall _ _) (by
            intro z hz
            exact (hsw ((show dist (z.1 : Cover) cubeCenter < r from hz).trans_le hrs)).le)
    have hglobal : (∫ z in S, W z ∂(μ : Measure NormalBundle)) ≤ ∫ z, W z ∂(μ : Measure NormalBundle) :=
      setIntegral_le_integral hi (Eventually.of_forall fun z ↦ interiorWallWeight_nonneg z.1)
    exact (mul_pos hm (by norm_num)).trans_le (hlow.trans hglobal)
  have hex : ∃ F : Cover → Cover, ∃ hF : AdmissibleField F,
      0 < ∫ z, W z*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    by_contra! hb
    exact (not_le_of_gt hIpos) (normalMeasure_weighted_saturation hμ W hb)
  obtain ⟨F,hF,hflux⟩ := hex
  change 0 < ∫ z, interiorWallWeight z.1*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) at hflux
  rw [normalMeasure_weighted_flux hμ interiorWallWeight_smooth interiorWallWeight_periodic hF] at hflux
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ interiorWallWeight x • F x) := interiorWallWeight_smooth.smul hF.1
  rw [flux_sum_components E hG] at hflux
  have hex : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ (interiorWallWeight x • F x) i) := by
    by_contra! hn
    exact (not_le_of_gt hflux) (Finset.sum_nonpos fun i hi ↦ hn i)
  obtain ⟨i,hi⟩ := hex
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (interiorWallWeight x • F x) i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hG
  obtain ⟨D,hDi,hDf⟩ := exists_wallVariation_of_function i hf
    (by intro n x; rw [interiorWallWeight_periodic,hF.2.1])
    (by intro x hx; rw [interiorWallWeight_face i x hx]; simp)
  exact ⟨D,by simpa only [hDi,hDf] using hi⟩

theorem isMinimizerAt_centered_multiplier_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ, ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function := by
  obtain ⟨D,hD⟩ := isMinimizerAt_exists_interior_positive_flux hV hE hmin hc hμ
  exact isMinimizerAt_exists_coordinate_multiplier hmin hE hμ D hD.ne'

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_centered_multiplier_oai := @OAI.CubicTorus.isMinimizerAt_centered_multiplier_oai
