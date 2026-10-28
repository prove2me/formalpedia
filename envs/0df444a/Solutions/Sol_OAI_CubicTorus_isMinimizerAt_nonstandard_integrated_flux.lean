-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:16:54.179991+00:00
-- url     : https://prove2.me/submissions/cca07713-40af-4ce4-97ad-47789ab1e685

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_standard_slab
import Theorems.Thm_OAI_CubicTorus_axial_integrated_flux_actual
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_CMC_sign
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_center_normal_unique
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_global_normal
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nonstandard_strict_octant
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_strict_normal_component_ne_zero_ae

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

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

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

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

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

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

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

lemma admissible_translate {F : Cover → Cover} (hF : AdmissibleField F) (a : Cover) :
    AdmissibleField (fun x => F (x + a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const), ?_, fun x => hF.2.2 _⟩
  intro n x
  change F ((x + latticeVector n) + a) = F (x + a)
  rw [add_right_comm, hF.2.1]

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma flux_translation {F : Cover → Cover} (hF : AdmissibleField F)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) := by
    exact (by fun_prop : Measurable (fun z : Torus => z + quotientMap a)) hE
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hpre]
  have hG := admissible_translate hF (-a)
  have hG' : AdmissibleField (fun y => F (y - a)) := by simpa [sub_eq_add_neg] using hG
  rw [← setIntegral_lift (continuous_divergence hG'.1) (divergence_periodic hG'.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

end CubicTorus

namespace CubicTorus

lemma perimeter_translation_le {E : Set Torus} (hE : MeasurableSet E) (a : Cover) :
    perimeter ((fun z => z + quotientMap a) ⁻¹' E) ≤ perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_translation hF a hE]
  have hG : AdmissibleField (fun y => F (y - a)) := by
    simpa [sub_eq_add_neg] using admissible_translate hF (-a)
  exact le_iSup_of_le (fun y => F (y - a)) (le_iSup_of_le hG le_rfl)

lemma perimeter_translation_measurable {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective a
  refine le_antisymm (perimeter_translation_le hE b) ?_
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap b) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  have hh := perimeter_translation_le hpre (-b)
  have he : (fun z : Torus => z + quotientMap (-b)) ⁻¹'
      ((fun z : Torus => z + quotientMap b) ⁻¹' E) = E := by
    ext z
    simp [quotientMap_neg]
  rwa [he] at hh

theorem perimeter_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp, ← perimeter_congr_ae he]
  exact perimeter_translation_measurable (measurableSet_toMeasurable _ _) a

lemma volume_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    torusVolume ((fun z => z + a) ⁻¹' E) = torusVolume E :=
  (measurePreserving_add_right torusVolume a).measure_preimage hE

lemma finitePerimeter_translation {E : Set Torus} (hE : FinitePerimeter E) (a : Torus) :
    FinitePerimeter ((fun z => z + a) ⁻¹' E) := by
  refine ⟨hE.1.preimage (measurePreserving_add_right torusVolume a).quasiMeasurePreserving, ?_⟩
  rw [perimeter_translation hE.1]
  exact hE.2

theorem isMinimizerAt_translation {E : Set Torus} {V : ℝ} (hE : IsMinimizerAt V E) (a : Torus) :
    IsMinimizerAt V ((fun z => z + a) ⁻¹' E) := by
  refine ⟨finitePerimeter_translation hE.1 a, ?_, ?_⟩
  · rw [volume_translation hE.1.1, hE.2.1]
  · intro F hF hvF
    rw [perimeter_translation hE.1.1]
    exact hE.2.2 F hF hvF

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

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Filter
open scoped Topology RealInnerProductSpace

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

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

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

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
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

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
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

namespace Periodic

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
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

lemma integrableOn_fundamentalCube_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Cover → F} (hf : Continuous f) : IntegrableOn f fundamentalCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedFundamentalCube).mono_set
    (fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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
namespace Periodic

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x; change (F (x + latticeVector m)) i = (F x) i; rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_variation_of_function i hc hpc
  simpa only [normalFirstVariation, hi, hf] using hH D

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
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

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

lemma coverTrace_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    coverTrace (l.smulRight v)=l v := by
  conv_rhs => rw [cover_decompose v]
  simp only [coverTrace,ContinuousLinearMap.smulRight_apply,PiLp.smul_apply,
    smul_eq_mul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma divergence_eq_coverTrace (F : Cover → Cover) (x : Cover) :
    divergence F x=coverTrace (fderiv ℝ F x) := rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma volumeSupport_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    volumeSupport ((fun z ↦ z+b) ⁻¹' E) = (fun z ↦ z+b) ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : ((fun z ↦ z+b) ⁻¹' E) ∩ Metric.ball a r =
      (fun z ↦ z+b) ⁻¹' (E ∩ Metric.ball (a+b) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,dist_add_right]
  rw [he,Measure.real_def,Measure.real_def,
    volume_translation (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    openRepresentative ((fun z ↦ z+b) ⁻¹' E) =
      (fun z ↦ z+b) ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_translation hE.compl]
  rfl

lemma frontier_openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    frontier (openRepresentative ((fun z ↦ z+b) ⁻¹' E)) =
      (fun z ↦ z+b) ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_translation hE b]
  exact (Homeomorph.addRight b).preimage_frontier _ |>.symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma translateNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (a : Cover) (z : NormalBundle) :
    F (translateNormal a z).1=F ((z.1 : Cover)-a) := by
  change F (representative (quotientMap z.1-quotientMap a))=F ((z.1 : Cover)-a)
  rw [← quotientMap_sub]
  exact periodic_representative hp _

theorem isNormalMeasure_translation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (a : Cover) :
    IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) (μ.map (translateNormal a)) := by
  constructor
  · have hm : ((μ.map (translateNormal a)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_translateNormal a)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_translation_measurable hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (translateNormal a) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_translateNormal a).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_translation hF a hE]
    have hG : AdmissibleField (fun x ↦ F (x-a)) := by
      simpa only [sub_eq_add_neg] using admissible_translate hF (-a)
    rw [← hμ.2 _ hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪(z.2 : Cover),F (translateNormal a z).1⟫=⟪(z.2 : Cover),F ((z.1 : Cover)-a)⟫
      rw [translateNormal_periodic_eval hF.2.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cofactorLinear_inner (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ⟪n,cofactorLinear L n⟫=coverTrace L-⟪n,L n⟫ := by
  simp only [cofactorLinear,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one,ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

lemma cofactorLinear_coordinate {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point)
    (i : Fin 3) (n : Cover) :
    cofactorLinear (fderiv ℝ (fun y ↦ f y • EuclideanSpace.single i 1) point) n=
      coordinateNormalVelocity i f point n := by
  rw [fderiv_smul_const hf]
  have ha : ((fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ))).adjoint n=
      ⟪n,EuclideanSpace.single i 1⟫ • gradient f point := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
      real_inner_smul_right,real_inner_smul_left,inner_gradient_left]
    ring
  simp only [cofactorLinear,coverTrace_smulRight,ha,coordinateNormalVelocity]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma variationField_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (variationField a) :=
  a.smooth.smul contDiff_const

lemma variationField_periodic (a : Variation) (m : Fin 3 → ℤ) (x : Cover) :
    variationField a (x+latticeVector m)=variationField a x := by
  simp only [variationField,a.periodic]

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_unit_normal_derivative {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hu : ∀ᶠ y in 𝓝 x, ‖N y‖=1) :
    (fderiv ℝ N x).adjoint (N x)=0 := by
  have he : (fun y ↦ ⟪N y,N y⟫)=ᶠ[𝓝 x](fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hu] with y hy
    rw [real_inner_self_eq_norm_sq,hy,one_pow]
  have hh := (hN.hasFDerivAt.inner ℝ hN.hasFDerivAt).fderiv
  have hz := he.fderiv_eq (𝕜 := ℝ)
  rw [hh] at hz
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : Cover →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,fderiv_const_apply,zero_apply] at hv
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  rw [real_inner_comm (fderiv ℝ N x v) (N x)] at hv
  nlinarith [real_inner_comm (N x) (fderiv ℝ N x v)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_contDiff_top {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  exact coverTraceCLM.contDiff.comp (hF.fderiv_right (by simp))

lemma tangentialDivergence_scalar_normal {N : Cover → Cover} {f : Cover → ℝ} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hf : DifferentiableAt ℝ f x)
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    tangentialDivergence (fun y ↦ f y • N y) x (N x)=f x*divergence N x := by
  have hd := (hf.hasFDerivAt.smul hN.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ f y • N y) x = _ at hd
  have hn := hu.self_of_nhds
  have hzero : ⟪N x,fderiv ℝ N x (N x)⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,smooth_unit_normal_derivative hN hu,inner_zero_left]
  unfold tangentialDivergence
  simp only [divergence_eq_coverTrace,hd,coverTrace_add,coverTrace_smul,
    coverTrace_smulRight,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,inner_add_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,hzero,mul_zero,mul_one]
  ring

theorem weakCMC_normal_extension {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H := by
  let f : Cover → ℝ := fun x ↦ divergence N x-H
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (divergence_contDiff_top hN).sub contDiff_const
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp only [f,divergence_periodic hp]
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • N x) := hf.smul hN
  have hFp : ∀ m x,(fun y ↦ f y • N y) (x+latticeVector m)=f x • N x := by
    intro m x
    change f (x+latticeVector m) • N (x+latticeVector m)=_
    rw [hfp,hp]
  have h := hCMC _ hF hFp
  have hl : (∫ z,tangentialDivergence (fun x ↦ f x • N x) z.1 z.2 ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1*divergence N z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [← hz.1,tangentialDivergence_scalar_normal
      (hN.differentiable (by simp) _) (hf.differentiable (by simp) _) hz.2]
  have hr : (∫ z,⟪(z.2 : Cover),f z.1 • N z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ z,f z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    filter_upwards [hn] with z hz
    rw [hz.1,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
  rw [hl,hr] at h
  have hfc : Continuous (fun z : NormalBundle ↦ f z.1) := hf.continuous.comp
    (continuous_subtype_val.comp continuous_fst)
  have hdc : Continuous (fun z : NormalBundle ↦ divergence N z.1) :=
    (continuous_divergence hN).comp (continuous_subtype_val.comp continuous_fst)
  have hi : Integrable (fun z : NormalBundle ↦ f z.1*divergence N z.1) (μ : Measure NormalBundle) :=
    (hfc.mul hdc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (fun z : NormalBundle ↦ H*f z.1) (μ : Measure NormalBundle) :=
    (hfc.const_mul H).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : (∫ z,(f z.1)^2 ∂(μ : Measure NormalBundle))=0 := by
    have he : (fun z : NormalBundle ↦ (f z.1)^2)=
        (fun z ↦ f z.1*divergence N z.1-H*f z.1) := by
      funext z
      dsimp [f]
      ring
    rw [he,integral_sub hi hi',integral_const_mul,h,sub_self]
  have his : Integrable (fun z : NormalBundle ↦ (f z.1)^2) (μ : Measure NormalBundle) :=
    (hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z : NormalBundle ↦ sq_nonneg (f z.1))) his).mp hs
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_denom_pos (v : Cover) :
    0<‖v‖^2+(1-Real.smoothTransition (4*‖v‖^2)) := by
  by_cases h : v=0
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma regularizedNormal_contDiff {R : Cover → Cover}
    (hR : ContDiff ℝ (⊤ : ℕ∞) R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNormal R) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ‖R x‖^2) := hR.norm_sq ℝ
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ ‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))) :=
    hq.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul hq)))
  exact ((hd.sqrt (fun x ↦ (regularizedNormal_denom_pos _).ne')).inv
    (fun x ↦ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)).ne')).smul hR

lemma regularizedNormal_eq {R : Cover → Cover} {x : Cover} (h : (1/4 : ℝ)≤‖R x‖^2) :
    regularizedNormal R x=‖R x‖⁻¹ • R x := by
  unfold regularizedNormal
  rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,add_zero,
    Real.sqrt_sq (norm_nonneg _)]

lemma regularizedNormal_unit_near {R : Cover → Cover} (hR : Continuous R) {x : Cover}
    (hx : (1/4 : ℝ)<‖R x‖^2) :
    ∀ᶠ y in 𝓝 x,‖regularizedNormal R y‖=1 := by
  have hnear : ∀ᶠ y in 𝓝 x,(1/4 : ℝ)<‖R y‖^2 :=
    (hR.norm.pow 2).continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [hnear] with y hy
  have hn : 0<‖R y‖ := lt_of_not_ge fun h ↦ by
    have hz := le_antisymm h (norm_nonneg _)
    rw [hz] at hy
    norm_num at hy
  rw [regularizedNormal_eq hy.le,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne']

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

lemma regularizedNormal_eventuallyEq {N : Cover → Cover} {x : Cover}
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : regularizedNormal N=ᶠ[𝓝 x]N := by
  filter_upwards [hu] with y hy
  rw [regularizedNormal_eq (by rw [hy]; norm_num),hy,inv_one,one_smul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_LatticeHeightHom
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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
namespace Periodic

lemma coordinateCMC_of_global {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (b : Variation) : normalFirstVariation μ b=H*directionalFlux E b.coordinate b.function := by
  have he := hCMC (variationField b) (variationField_smooth b) (variationField_periodic b)
  rw [periodic_normal_flux hμ (variationField_smooth b) (variationField_periodic b)] at he
  have hleft : normalFirstVariation μ b=
      ∫ z,tangentialDivergence (variationField b) z.1 z.2 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      change ⟪(z.2 : Cover),coordinateNormalVelocity b.coordinate b.function z.1 z.2⟫=_
      rw [← cofactorLinear_coordinate (b.smooth.differentiable (by simp) z.1),
        cofactorLinear_inner _ z.2.property]
      rfl
  rw [hleft,he]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ divergence_smul_const (b.smooth.differentiable (by simp) x) _

end Periodic
end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace LatticeIsometry

lemma measurePreserving (e : LatticeIsometry) : MeasurePreserving e.torus torusVolume torusVolume :=
  (e.addHom).measurePreserving e.torus.continuous e.torus.surjective rfl

end LatticeIsometry

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingReflectNormal
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

theorem isMinimizerAt_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N x=w := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [←quotientMap_add,show cubeCenter+a=x by dsimp [a]; abel]
    exact hx
  obtain ⟨w,hw⟩ := isMinimizerAt_center_normal_unique hV hE' hmin' hc
  refine ⟨w,?_⟩
  intro μ hμ N hN hp hae
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hh := hw (μ.map (translateNormal a)) (isNormalMeasure_translation hE hμ a)
    N' hN' hp' hae'
  change N (cubeCenter+a)=w at hh
  simpa only [show cubeCenter+a=x by dsimp [a]; abel] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_OctantVertex
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

lemma smooth_periodic_centered_primitive {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.Periodic ψ 1 ∧
      ∀ t,deriv ψ t=f t-∫ u in (0 : ℝ)..1,f u := by
  let c : ℝ := ∫ u in (0 : ℝ)..1,f u
  let g : ℝ → ℝ := fun t ↦ f t-c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hgp : Function.Periodic g 1 := fun t ↦ by simp [g,hp t]
  let ψ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t,g u
  have hd (t : ℝ) : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun t ↦ (hd t).differentiableAt,(funext fun t ↦ (hd t).deriv) ▸ hg⟩
  have hz : (∫ u in (0 : ℝ)..1,g u)=0 := by
    rw [show g=(fun t ↦ f t-c) from rfl,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
        intervalIntegrable_const,intervalIntegral.integral_const]
    simp [c]
  refine ⟨ψ,hψ,?_,fun t ↦ (hd t).deriv⟩
  intro t
  change (∫ u in (0 : ℝ)..t+1,g u)=∫ u in (0 : ℝ)..t,g u
  rw [hgp.intervalIntegral_add_eq_add 0 t (fun _ _ ↦ hg.continuous.intervalIntegrable _ _)]
  simp only [zero_add,hz,add_zero]

lemma axial_scalar_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (i : Fin 3) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa only [PiLp.add_apply,latticeVector,WithLp.ofLp_toLp,mul_one] using hp.int_mul (m i) (x i)

lemma axial_scalar_fderiv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i : Fin 3) (x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ f (y i)) x v=deriv f (x i)*v i := by
  have hh := (hf (x i)).hasDerivAt.comp_hasFDerivAt x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : Cover ↦ f (y i)) _ x at hh
  rw [hh.fderiv]
  rfl

lemma axial_field_tangentialDivergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x ν : Cover) :
    tangentialDivergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x ν=
      deriv f (x i)*(1-(ν i)^2) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [tangentialDivergence_smul_const hd,axial_scalar_fderiv hf]
  simp [tangentPart,EuclideanSpace.inner_single_right,pow_two]

lemma axial_field_divergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Cover) :
    divergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x=deriv f (x i) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [divergence_smul_const hd,axial_scalar_fderiv hf]
  simp

theorem sibling_axial_flux_derivative {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : Function.Periodic ψ 1) :
    (∫ z,deriv ψ ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))=
      H*∫ x in fundamentalCube∩quotientMap ⁻¹' E,deriv ψ (x i) := by
  have hfield : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Cover ↦ ψ (x i) • (EuclideanSpace.single i 1 : Cover)) :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hh := Periodic.tangent_firstVariation_of_coordinate hH hfield (fun m x ↦ by
    rw [axial_scalar_periodic hp i m x])
  simpa only [axial_field_tangentialDivergence (hψ.differentiable (by simp)),
    axial_field_divergence (hψ.differentiable (by simp))] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_flux_marginal {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  obtain ⟨ψ,hψ,hψp,hd⟩ := smooth_periodic_centered_primitive hf hp
  have hh := sibling_axial_flux_derivative hH i hψ hψp
  simp_rw [hd,sub_mul] at hh
  have hiV : IntegrableOn (fun x : Cover ↦ f (x i))
      (fundamentalCube∩quotientMap ⁻¹' E) :=
    (integrableOn_fundamentalCube_of_continuous
      (hf.continuous.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous)).mono_set inter_subset_left
  rw [integral_sub (normal_axial_integrable μ i hf.continuous)
      ((normal_transverse_integrable μ i).const_mul _),integral_const_mul,
    integral_sub hiV (integrable_const _),integral_const] at hh
  simp only [Measure.real_def,Measure.restrict_apply_univ,smul_eq_mul] at hh
  change _-_ = H*(_-volume.real (fundamentalCube∩quotientMap ⁻¹' E)*_) at hh
  unfold axialTransverseMass
  nlinarith [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_stationary_tubular_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := by
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hpoint (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      ‖N x‖=1 ∧ divergence N x=H := by
    constructor
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
        continuous_const (fun m y ↦ by rw [hp]) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hn] with z hz
      rw [hz.1,z.2.property]
    · exact isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ (continuous_divergence hN)
        continuous_const (divergence_periodic hp) (fun _ _ ↦ rfl) hH x hx
  have hR := regularizedNormal_contDiff hN
  have hrp : ∀ m x,regularizedNormal N (x+latticeVector m)=regularizedNormal N x := by
    intro m x
    simp only [regularizedNormal,hp]
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),regularizedNormal N=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hn] with z hz
    exact regularizedNormal_eventuallyEq hz.2
  refine ⟨regularizedNormal N,hR,hrp,?_,?_⟩
  · filter_upwards [hn,he] with z hz hze
    exact hze.eq_of_nhds.trans hz.1
  · intro x hx
    refine ⟨regularizedNormal_unit_near hN.continuous (by rw [(hpoint x hx).1]; norm_num),?_⟩
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) (continuous_divergence hN)
      (divergence_periodic hrp) (divergence_periodic hp) _ x hx |>.trans (hpoint x hx).2
    filter_upwards [he] with z hz
    simp only [divergence_eq_coverTrace,hz.fderiv_eq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalSphere_sum_sq (ν : NormalSphere) : (∑ i : Fin 3,((ν : Cover) i)^2)=1 := by
  have hh := real_inner_self_eq_norm_sq (ν : Cover)
  rw [ν.property,one_pow] at hh
  simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,←pow_two] using hh

lemma normalSphere_coordinate_sq_le (ν : NormalSphere) (i : Fin 3) : ((ν : Cover) i)^2≤1 := by
  exact (Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) ↦ sq_nonneg ((ν : Cover) j))
    (Finset.mem_univ i)).trans_eq (normalSphere_sum_sq ν)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma circleMollifier_tendsto : Tendsto (fun n ↦ (circleMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [circleMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma circleSmoothApprox_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed hf.locallyIntegrable

lemma circleSmoothApprox_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n ↦ circleSmoothApprox f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous circleMollifier_tendsto hf x

lemma circleSmoothApprox_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ x,‖f x‖≤C)
    (n : ℕ) (x : ℝ) : ‖circleSmoothApprox f n x‖≤C := by
  rw [circleSmoothApprox,convolution_def]
  calc
    _ ≤ ∫ y : ℝ,(circleMollifier n).normed volume y*C := by
      apply norm_integral_le_of_norm_le ((circleMollifier n).integrable_normed.mul_const C)
      filter_upwards [] with y
      rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg ((circleMollifier n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hb (x-y)) ((circleMollifier n).nonneg_normed y)
    _ = C := by rw [integral_mul_const,(circleMollifier n).integral_normed,one_mul]

lemma circleSmoothApprox_integral_tendsto {α : Type*} [MeasurableSpace α]
    {η : Measure α} {g w : α → ℝ} (hg : Measurable g) (hw : Integrable w η)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x)*w x ∂η) atTop
      (𝓝 (∫ x,f (g x)*w x ∂η)) := by
  obtain ⟨C,hC⟩ := (hp.isBounded_of_continuous (by norm_num) hf).exists_norm_le
  have hbound (t : ℝ) : ‖f t‖≤C := hC _ ⟨t,rfl⟩
  apply tendsto_integral_of_dominated_convergence (fun x ↦ C*‖w x‖)
  · intro n
    exact (((circleSmoothApprox_contDiff hf n).continuous.measurable.comp hg).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  · exact hw.norm.const_mul C
  · intro n
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (circleSmoothApprox_bound hbound n (g x)) (norm_nonneg _)
  · filter_upwards [] with x
    exact (circleSmoothApprox_tendsto hf (g x)).mul tendsto_const_nhds

lemma circleSmoothApprox_integral_tendsto_finite {α : Type*} [MeasurableSpace α]
    {η : Measure α} [IsFiniteMeasure η] {g : α → ℝ} (hg : Measurable g)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x) ∂η) atTop
      (𝓝 (∫ x,f (g x) ∂η)) := by
  simpa only [mul_one] using circleSmoothApprox_integral_tendsto hg
    (integrable_const (1 : ℝ) (μ := η)) hf hp

theorem axial_flux_marginal_continuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  let A := fundamentalCube∩quotientMap ⁻¹' E
  have hA : volume A≠⊤ := ne_top_of_le_ne_top (by rw [volume_fundamentalCube]; exact ENNReal.one_ne_top)
    (measure_mono inter_subset_left)
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hA.lt_top⟩
  have hs := circleSmoothApprox_integral_tendsto
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst).measurable)
    (normal_transverse_integrable μ i) hf hp
  have hv := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict A)
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).measurable hf hp
  have ht := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict (Ioc (0 : ℝ) 1))
    measurable_id hf hp
  have ht' : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1,circleSmoothApprox f n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1,f t)) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),id_eq] using ht
  have hleft := hs.sub (hv.const_mul H)
  have hright := ht'.const_mul (axialTransverseMass μ i-H*volume.real A)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [] with n
  exact (axial_flux_marginal hH i (circleSmoothApprox_contDiff hf n)
    (circleSmoothApprox_periodic hp n)).symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AxisCircleLebesgue
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

lemma axialSurfaceMarginal_integral (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)),smul_eq_mul,mul_comm]

lemma axialVolumeMarginal_integral (E : Set Torus) (i : Fin 3)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun x : Cover ↦ (x i : AxisCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable]

lemma axisCircleLebesgue_integral {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle))=
      ∫ t in (0 : ℝ)..1,f (t : AxisCircle) := by
  change (∫ t,f t ∂Measure.map _ _)=_
  have hc : Continuous (fun t : ℝ ↦ (t : AxisCircle)) := AddCircle.continuous_mk' (1 : ℝ)
  rw [integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]

lemma axial_circle_flux_integral {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        (∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := by
  rw [axialSurfaceMarginal_integral μ i hf,axialVolumeMarginal_integral E i hf,
    axisCircleLebesgue_integral hf]
  have hc : Continuous (fun t : ℝ ↦ f (t : AxisCircle)) := hf.comp (AddCircle.continuous_mk' (1 : ℝ))
  exact axial_flux_marginal_continuous hH i hc
    (fun t ↦ by change f ((t+1 : ℝ) : AxisCircle)=f (t : AxisCircle); rw [AddCircle.coe_add_period])

theorem axial_circle_flux_measure {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    let c := axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E)
    (axialSurfaceMarginal μ i : Measure AxisCircle)+
      Real.toNNReal (-H) • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal (-c) • (axisCircleLebesgue : Measure AxisCircle)=
      Real.toNNReal H • (axialVolumeMarginal E i : Measure AxisCircle)+
      Real.toNNReal c • (axisCircleLebesgue : Measure AxisCircle) := by
  intro c
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hi (η : Measure AxisCircle) [IsFiniteMeasure η] : Integrable f η := f.integrable
  rw [integral_add_measure (hi _) (hi _),integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal']
  have hh := axial_circle_flux_integral hH i f.continuous
  change _-H*_=c*_ at hh
  have split (a : ℝ) : max a 0-max (-a) 0=a := by
    rcases le_total 0 a with ha|ha
    · simp only [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha),sub_zero]
    · simp only [max_eq_right ha,max_eq_left (neg_nonneg.mpr ha),zero_sub,neg_neg]
  have hh' : (∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle))-
      H*(∫ t,f t ∂(axialVolumeMarginal E i : Measure AxisCircle))=
      c*(∫ t,f t ∂(axisCircleLebesgue : Measure AxisCircle)) := hh
  rw [←split H,←split c] at hh'
  linarith only [hh']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircleLebesgue_eq_volume : (axisCircleLebesgue : Measure AxisCircle)=volume := by
  change Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1))=volume
  exact (show MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle))
    (volume.restrict (Ioc 0 1)) volume from by simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

lemma torus_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus ↦ x i) torusVolume (volume : Measure AxisCircle) := by
  have he := measurePreserving_eval (fun _ : Fin 3 ↦ (volume : Measure AxisCircle)) i
  rw [←volume_pi] at he
  exact he.comp torus_to_product_measurePreserving

lemma cube_axis_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Cover ↦ (x i : AxisCircle))
      (volume.restrict fundamentalCube) volume :=
  (torus_axis_measurePreserving i).comp quotientMap_measurePreserving

lemma axialVolumeMarginal_le (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≤volume := by
  change Measure.map (fun x : Cover ↦ (x i : AxisCircle))
    (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))≤volume
  rw [←(cube_axis_measurePreserving i).map_eq]
  exact Measure.map_mono (Measure.restrict_mono inter_subset_left le_rfl)
    (cube_axis_measurePreserving i).measurable

lemma axialVolumeMarginal_absolutelyContinuous (E : Set Torus) (i : Fin 3) :
    (axialVolumeMarginal E i : Measure AxisCircle)≪volume :=
  (axialVolumeMarginal_le E i).absolutelyContinuous

theorem axialSurfaceMarginal_absolutelyContinuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hv := axialVolumeMarginal_absolutelyContinuous E i hz
  have hh := congrArg (fun η : Measure AxisCircle ↦ η s) (axial_circle_flux_measure hH i)
  simp only [Measure.add_apply,Measure.smul_apply,axisCircleLebesgue_eq_volume,hz,hv,smul_zero,
    add_zero] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_axisCircle_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst)

lemma normalSphere_two_sq_le (ν : NormalSphere) {i j : Fin 3} (hij : i≠j) :
    ((ν : Cover) i)^2+((ν : Cover) j)^2≤1 := by
  have ht : i∈({i,j} : Finset (Fin 3)) := by simp
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i,j} : Finset (Fin 3))⊆Finset.univ from Finset.subset_univ _)
    (fun k _ _ ↦ sq_nonneg ((ν : Cover) k))
  simpa only [Finset.sum_pair hij,normalSphere_sum_sq] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaMarginal
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

lemma normal_transverse_positive_ae {μ : FiniteMeasure NormalBundle}
    (hn : ∀ i : Fin 3,∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0) (i : Fin 3) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),0<1-((z.2 : Cover) i)^2 := by
  let j := i.succAbove (0 : Fin 2)
  have hji : j≠i := Fin.succAbove_ne i 0
  filter_upwards [hn j] with z hz
  have hh := normalSphere_two_sq_le z.2 hji
  have hj := sq_pos_of_ne_zero hz
  linarith

theorem axialAreaMarginal_absolutelyContinuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hn : ∀ i : Fin 3,∀ᵐ z ∂(μ : Measure NormalBundle),((z.2 : Cover) i)≠0) (i : Fin 3) :
    (axialAreaMarginal μ i : Measure AxisCircle)≪volume := by
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  have hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),ENNReal.ofReal (1-((z.2 : Cover) i)^2)≠0 := by
    filter_upwards [normal_transverse_positive_ae hn i] with z hz
    exact (ENNReal.ofReal_pos.mpr hz).ne'
  have hac := withDensity_absolutelyContinuous' hw.aemeasurable hpos
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := axialSurfaceMarginal_absolutelyContinuous hH i hz
  change Measure.map _ _ s=0 at hh
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh
  change Measure.map _ _ s=0
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs]
  exact hac hh

lemma isMinimizerAt_nonstandard_strict_signs_of_actual_normal {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ b : Fin 3 → Bool,∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0 := by
  obtain ⟨μ',H',N',b,hμ',hN',hp',hae',hb',hsg,_⟩ :=
    isMinimizerAt_nonstandard_strict_octant hV hmin hc hstd hR
  refine ⟨b,?_⟩
  intro i x hxi hx
  obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique ⟨hV.1,by linarith [hV.2]⟩ hE hmin x hx
  have he := (hw μ hμ N hN hp hae).trans (hw μ' hμ' N' hN' hp' hae').symm
  rw [he]
  exact hsg i x hxi hx

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
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

lemma congruentAE_congr_ae_left {E F K : Set Torus} (h : E=ᵐ[torusVolume]F) :
    CongruentAE E K ↔ CongruentAE F K := by
  constructor
  · rintro ⟨φ,hφ⟩; exact ⟨φ,h.symm.trans hφ⟩
  · rintro ⟨φ,hφ⟩; exact ⟨φ,h.trans hφ⟩

lemma smallStandardRegion_congr_ae {E F : Set Torus} (h : E=ᵐ[torusVolume]F) (V : ℝ) :
    SmallStandardRegion V E ↔ SmallStandardRegion V F := by
  simp only [SmallStandardRegion,congruentAE_congr_ae_left h]

lemma standardRegionAt_congr_ae {E F : Set Torus} (h : E=ᵐ[torusVolume]F) (V : ℝ) :
    StandardRegionAt V E ↔ StandardRegionAt V F := by
  have hh : Eᶜ=ᵐ[torusVolume]Fᶜ := by
    filter_upwards [h] with x hx
    exact congrArg Not hx
  unfold StandardRegionAt
  split_ifs
  · exact smallStandardRegion_congr_ae h V
  · exact smallStandardRegion_congr_ae hh (1-V)

end CubicTorus

end
end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_openRepresentative_ae_nullMeasurable {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : openRepresentative E =ᵐ[torusVolume] E := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).2 hmin
  have hUF := isMinimizerAt_openRepresentative_ae hV hF hmF
  rw [openRepresentative_congr_ae hFE] at hUF
  exact hUF.trans hFE

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
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

theorem isMinimizerAt_nonstandard_integrated_flux_oai {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,Nesting.lambda*axialTransverseMass μ i+
        (∫ t,Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/
          axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae_nullMeasurable hV' hmin
  have hmO := (isMinimizerAt_congr_ae hOE).mpr hmin
  have hsO : ¬StandardRegionAt V O := fun hs ↦ hstd ((standardRegionAt_congr_ae hOE V).mp hs)
  have hcO : IsPreconnected (frontier (openRepresentative O)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV' hmO).resolve_right (fun h ↦ hsO h.2.2)
  have hRO (i : Fin 3) : O=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' O) :=
    hOE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hOE.symm))
  obtain ⟨μ,H,hμ,hCMC,_,_⟩ := isMinimizerAt_CMC_sign hV' hO hmO
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV' hO hmO hμ hCMC
  obtain ⟨b,hsg⟩ := isMinimizerAt_nonstandard_strict_signs_of_actual_normal hV hO hmO hcO hsO hRO hμ hN hp hae
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hn (i : Fin 3) := strict_normal_component_ne_zero_ae hV' hO hmO hRO hμ hH hN hp hae hsg i
  have ha (i : Fin 3) := axialAreaMarginal_absolutelyContinuous hH hn i
  refine ⟨μ,H,hμ.congr_ae hOE,hCMC,ha,fun i ↦ ?_⟩
  have hh := axial_integrated_flux_actual hO hμ hH i (ha i)
  rwa [perimeter_congr_ae hOE] at hh

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux_oai := @OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux_oai
