-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_planar_profile_circle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:19:15.759176+00:00
-- url     : https://prove2.me/submissions/1fede879-c458-4595-a492-a917efeeb1f9

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_boundary_slice_null_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_corner_boundary_heights_null
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_planar_profile

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

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

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

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_TransverseTorus
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

lemma sibling_torusCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Torus) (i : Fin 3) :
    torusCoordinatePermute e x i=x (e i) := rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalMap
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
namespace LatticeIsometry

lemma volumeSupport_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    volumeSupport (e.torus ⁻¹' E)=e.torus ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (e.torus ⁻¹' E)∩Metric.ball a r=e.torus ⁻¹' (E∩Metric.ball (e.torus a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,e.torus.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,e.measurePreserving.measure_preimage
    (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    openRepresentative (e.torus ⁻¹' E)=e.torus ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [←preimage_compl,e.volumeSupport_preimage hE.compl]
  rfl

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_torus_apply (i j : Fin 3) (x : Torus) :
    (axisReflection i).torus x j=if j=i then -x j else x j := by
  classical
  change (torusCoordinatePermute (Equiv.swap 0 i)
    (torusFirstReflection (torusCoordinatePermute (Equiv.swap 0 i) x))) j=_
  simp only [sibling_torusCoordinatePermute_apply,torusFirstReflection_apply,Equiv.swap_apply_self]
  by_cases h : j=i
  · subst j
    simp
  · have : Equiv.swap (0 : Fin 3) i j≠0 := by
      intro he
      have := congrArg (Equiv.swap (0 : Fin 3) i) he
      exact h (by simpa using this)
    simp [h,this]

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

lemma LatticeIsometry.openRepresentative_preimage_null (e : LatticeIsometry)
    {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    openRepresentative (e.torus ⁻¹' E)=e.torus ⁻¹' openRepresentative E := by
  have he := hE.toMeasurable_ae_eq
  have hp := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [←openRepresentative_congr_ae hp,e.openRepresentative_preimage (measurableSet_toMeasurable _ _),
    openRepresentative_congr_ae he]

lemma reflection_invariant_openRepresentative {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈openRepresentative E ↔ z∈openRepresentative E := by
  intro i z
  have hh := openRepresentative_congr_ae (hR i)
  rw [(axisReflection i).openRepresentative_preimage_null hE] at hh
  exact (Set.ext_iff.mp hh z).symm

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

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

lemma axialSliceVolume_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (axialSliceVolume E i) := by
  exact measurable_measure_prodMk_left (hE.preimage (torusAxialSplit i).symm.measurable)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalTransverseLength
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

lemma axialSliceIntegral_indicator {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (f : Torus → ℝ) (t : AxisCircle) :
    axialSliceIntegral E i f t=∫ y,E.indicator f ((torusAxialSplit i).symm (t,y)) := by
  rw [axialSliceIntegral,←integral_indicator (axialSlice_measurable hE i t)]
  congr 1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisEmbedding_norm (i : Fin 3) (y : Plane) : ‖planeAxisEmbedding i y‖=‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
  simp

lemma planeAxisProjection_norm_le (i : Fin 3) (x : Cover) : ‖planeAxisProjection i x‖≤‖x‖ := by
  have hh : ‖planeAxisProjection i x‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succAbove _ i]
    simp only [planeAxisProjection_apply]
    nlinarith [sq_nonneg ‖x i‖]
  nlinarith [norm_nonneg (planeAxisProjection i x),norm_nonneg x]

lemma liftPlanarField_admissible (i : Fin 3) {G : Plane → Plane}
    (hG : PlanarAdmissibleField G) : AdmissibleField (liftPlanarField i G) := by
  refine ⟨(planeAxisEmbedding i).contDiff.comp (hG.1.comp (planeAxisProjection i).contDiff),?_,?_⟩
  · intro n x
    unfold liftPlanarField
    rw [map_add]
    exact congrArg (planeAxisEmbedding i) (hG.2.1 (fun j ↦ n (i.succAbove j)) _)
  · intro x
    rw [liftPlanarField,planeAxisEmbedding_norm]
    exact hG.2.2 _

lemma divergence_liftPlanarField (i : Fin 3) {G : Plane → Plane}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    divergence (liftPlanarField i G) x=planeDivergence G (planeAxisProjection i x) := by
  have hd := (planeAxisEmbedding i).hasFDerivAt.comp x
    (((hG.differentiable (by simp) (planeAxisProjection i x)).hasFDerivAt).comp x
      (planeAxisProjection i).hasFDerivAt)
  change HasFDerivAt (liftPlanarField i G) _ x at hd
  rw [divergence,hd.fderiv,Fin.sum_univ_succAbove _ i]
  simp [ContinuousLinearMap.comp_apply,planeDivergence,Fin.sum_univ_two]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeAxisAt_contDiff (i : Fin 3) (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (planeAxisAt i a) :=
  contDiff_const.add (planeAxisEmbedding i).contDiff

lemma planeAxisAt_hasFDerivAt (i : Fin 3) (a : ℝ) (y : Plane) :
    HasFDerivAt (planeAxisAt i a) (planeAxisEmbedding i) y := by
  exact (planeAxisEmbedding i).hasFDerivAt.const_add (a • EuclideanSpace.single i (1 : ℝ))

lemma tracePlanarField_admissible (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : AdmissibleField F) : PlanarAdmissibleField (tracePlanarField i a F) := by
  refine ⟨(planeAxisProjection i).contDiff.comp (hF.1.comp (planeAxisAt_contDiff i a)),?_,?_⟩
  · intro n y
    have he : planeAxisAt i a (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        planeAxisAt i a y+latticeVector (i.insertNth (α := fun _ : Fin 3 ↦ ℤ) 0 n) := by
      ext k
      rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
        simp [latticeVector,planeAxisAt,map_add,add_assoc]
    unfold tracePlanarField
    rw [he,hF.2.1]
  · intro y
    exact (planeAxisProjection_norm_le i _).trans (hF.2.2 _)

lemma planeDivergence_tracePlanarField (i : Fin 3) (a : ℝ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFi : ∀ x,F x i=0) (y : Plane) :
    planeDivergence (tracePlanarField i a F) y=divergence F (planeAxisAt i a y) := by
  have hd := (planeAxisProjection i).hasFDerivAt.comp y
    (((hF.differentiable (by simp) (planeAxisAt i a y)).hasFDerivAt).comp y
      (planeAxisAt_hasFDerivAt i a y))
  change HasFDerivAt (tracePlanarField i a F) _ y at hd
  have hz : (fderiv ℝ F (planeAxisAt i a y) (EuclideanSpace.single i 1)) i=0 := by
    rw [←fderiv_component (hF.differentiable (by simp) _) i]
    simp only [hFi]
    simp
  rw [planeDivergence,hd.fderiv,divergence,Fin.sum_univ_succAbove _ i,hz]
  simp [ContinuousLinearMap.comp_apply,Fin.sum_univ_two]

lemma planeAxisProjection_representative (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    planeAxisProjection i (representative ((torusAxialSplit i).symm (t,y)))=planarRepresentative y := by
  ext j
  simp [representative,planarRepresentative]

lemma representative_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    representative ((torusAxialSplit i).symm (t,y))=
      planeAxisAt i (((AddCircle.equivIco (1 : ℝ) 0) t) : ℝ) (planarRepresentative y) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩ <;>
    simp [representative,planarRepresentative]

theorem axialTestPerimeter_eq_planar (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialTestPerimeter E i t=planarTorusPerimeter (axialSlice E i t) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let a : ℝ := ((AddCircle.equivIco (1 : ℝ) 0) t : ℝ)
    have hb : ENNReal.ofReal (∫ y in axialSlice E i t,
        planeDivergence (tracePlanarField i a F) (planarRepresentative y))≤
        planarTorusPerimeter (axialSlice E i t) :=
      le_iSup_of_le (tracePlanarField i a F)
        (le_iSup_of_le (tracePlanarField_admissible i a hF) le_rfl)
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [planeDivergence_tracePlanarField i a hF.1 hFi,representative_axialSplit]
  · refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
    have hb : ENNReal.ofReal (axialSliceIntegral E i
        (fun z ↦ divergence (liftPlanarField i G) (representative z)) t)≤axialTestPerimeter E i t :=
      le_iSup_of_le (liftPlanarField i G)
        (le_iSup_of_le (liftPlanarField_admissible i hG)
          (le_iSup_of_le (liftPlanarField_same i G) le_rfl))
    apply le_trans _ hb
    apply le_of_eq
    congr 1
    unfold axialSliceIntegral
    apply integral_congr_ae
    filter_upwards [] with y
    rw [divergence_liftPlanarField i hG.1,planeAxisProjection_representative]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SmoothSeamProbability
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

theorem isMinimizerAt_planar_profile_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) :
    ∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),
      ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hc : ∀ᵐ t : ℝ,∀ n : Fin 2 →Bool,
      quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E) := by
    rw [ae_all_iff]
    intro n
    exact (ae_iff.mpr (by simpa only [not_not] using isMinimizerAt_corner_boundary_heights_null hV hE hmin hR b i n))
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hn := hp.quasiMeasurePreserving.ae (isMinimizerAt_boundary_slice_null_ae hV hE hmin i)
  have hsub : Icc (1/2 : ℝ) 1⊆Ioc 0 1 := fun t ht ↦ ⟨by linarith [ht.1],ht.2⟩
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae_restrict_of_subset hsub hn,
    ae_restrict_mem measurableSet_Icc] with t htc htn ht
  exact isMinimizerAt_section_planar_profile hV hmin hR hd i ht htc htn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Measurable f) : Measurable (axialSliceIntegral E i f) := by
  have hh := ((hf.indicator hE).comp (torusAxialSplit i).symm.measurable).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure TransverseProduct))
  simpa only [Function.comp_apply,←axialSliceIntegral_indicator hE] using hh.measurable

lemma axialTestPerimeter_countable (i : Fin 3) :
    ∃ S : Set C(Torus,ℝ),S⊆axialDivergenceClass i ∧ S.Countable ∧
      ∀ (E : Set Torus) (t : AxisCircle),axialTestPerimeter E i t=
        ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f) := by
  obtain ⟨S,hS,hSc,hSd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace (axialDivergenceClass i)).exists_countable_dense_subset
  refine ⟨S,hS,hSc,?_⟩
  intro E t
  apply le_antisymm
  · refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ?_
    let f : C(Torus,ℝ) := ⟨fun z ↦ divergence F (representative z),
      continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩
    have hf : f∈axialDivergenceClass i := ⟨F,hF,hFi,rfl⟩
    let r : ℝ≥0∞ := ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f)
    have hc : IsClosed {f : C(Torus,ℝ) | ENNReal.ofReal (axialSliceFunctional E i t f) ≤ r} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (axialSliceFunctional E i t).continuous) continuous_const
    have hh : S⊆{f : C(Torus,ℝ) | ENNReal.ofReal (axialSliceFunctional E i t f) ≤ r} := by
      intro f hf
      exact le_iSup (fun f : S ↦ ENNReal.ofReal (axialSliceFunctional E i t f)) ⟨f,hf⟩
    exact (closure_minimal hh hc) (hSd hf)
  · apply iSup_le
    intro f
    obtain ⟨F,hF,hFi,hfe⟩ := hS f.property
    have he : axialSliceFunctional E i t f=
        axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t := by
      change axialSliceIntegral E i f t=_
      rw [hfe]
      rfl
    rw [he]
    exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hFi le_rfl))

theorem planarTorusPerimeter_slice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (fun t : AxisCircle ↦ planarTorusPerimeter (axialSlice E i t)) := by
  obtain ⟨S,hS,hSc,he⟩ := axialTestPerimeter_countable i
  have : Countable S := hSc.to_subtype
  have hh : Measurable (fun t : AxisCircle ↦ ⨆ f : S,ENNReal.ofReal (axialSliceFunctional E i t f)) := by
    apply Measurable.iSup
    intro f
    exact (axialSliceIntegral_measurable hE i f.1.continuous.measurable).ennreal_ofReal
  simpa only [←he,axialTestPerimeter_eq_planar] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_axialSplit (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    (axisReflection i).torus ((torusAxialSplit i).symm (t,y))=
      (torusAxialSplit i).symm (-t,y) := by
  ext j
  rw [axisReflection_torus_apply]
  by_cases hj : j=i
  · subst j; simp
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Fin.succAbove_ne]

lemma axialSlice_neg_of_reflection {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (i : Fin 3) (t : AxisCircle) : axialSlice O i (-t)=axialSlice O i t := by
  ext y
  change (torusAxialSplit i).symm (-t,y)∈O ↔ (torusAxialSplit i).symm (t,y)∈O
  rw [←axisReflection_axialSplit]
  exact hR i _

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SharpSectionWeight
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

lemma circle_ae_of_upper_half {P : AxisCircle → Prop}
    (hm : MeasurableSet {t | P t})
    (hs : ∀ t,P (-t) ↔ P t)
    (hP : ∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),P (t : AxisCircle)) :
    ∀ᵐ t : AxisCircle,P t := by
  have hneg := ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Icc).mp hP)
  have hlo : ∀ᵐ t : ℝ,t∈Icc 0 (1/2 : ℝ) → P (t : AxisCircle) := by
    filter_upwards [hneg] with t ht hmem
    have hh := ht ⟨by linarith [hmem.2],by linarith [hmem.1]⟩
    have he : ((1-t : ℝ) : AxisCircle)=-(t : AxisCircle) := by
      rw [AddCircle.coe_sub]
      simp
    rw [he] at hh
    exact (hs _).mp hh
  have hall : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),P (t : AxisCircle) := by
    filter_upwards [ae_restrict_of_ae hlo,ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).mp hP),
      ae_restrict_mem measurableSet_Ioc] with t hl hu ht
    by_cases h : t≤1/2
    · exact hl ⟨le_of_lt ht.1,h⟩
    · exact hu ⟨le_of_lt (lt_of_not_ge h),ht.2⟩
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [←hp.map_eq]
  exact ae_map_iff hp.measurable.aemeasurable hm |>.mpr hall

theorem isMinimizerAt_planar_profile_circle_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) :
    ∀ᵐ t : AxisCircle,
      ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i t)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  apply circle_ae_of_upper_half
  · apply measurableSet_le
    · apply Measurable.ennreal_ofReal
      have hc : Continuous unitPlanarProfile := by unfold unitPlanarProfile; fun_prop
      exact hc.measurable.comp (axialSliceVolume_measurable (isOpen_openRepresentative E).measurableSet i).ennreal_toReal
    · exact planarTorusPerimeter_slice_measurable (isOpen_openRepresentative E).measurableSet i
  · intro t
    rw [axialSlice_neg_of_reflection (reflection_invariant_openRepresentative hmin.1.1 hR)]
  · exact isMinimizerAt_planar_profile_ae hV hE hmin hR hd i

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_planar_profile_circle_oai := @OAI.CubicTorus.isMinimizerAt_planar_profile_circle_oai
