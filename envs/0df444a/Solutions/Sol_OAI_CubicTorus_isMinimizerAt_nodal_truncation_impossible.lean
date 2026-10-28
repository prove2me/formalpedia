-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:16:06.799204+00:00
-- url     : https://prove2.me/submissions/a7318e41-0208-45f3-a280-9d4ee320fdb7

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_CenteredJacobiChart_nodal_truncation_impossible
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_centeredJacobiChart

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
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

lemma normalComponentScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (x : Cover) :
    (normalComponentScalar N hN hp i).val x=N x i := by
  simp only [normalComponentScalar,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
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

lemma directionalNormalScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v x : Cover) :
    (directionalNormalScalar N hN hp v).val x=⟪v,N x⟫ := by
  simp only [directionalNormalScalar,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,normalComponentScalar_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NodalTorusScalar
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

lemma positiveNodalPiece_subset (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) : D⊆S := by
  intro a ha
  rw [hD.1.choose_spec.2] at ha
  exact ha.1.1

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalizedCMCCharts
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

lemma smoothScalarTranslate_gradient (a : Cover) (f : smoothPeriodicScalars) (x : Cover) :
    gradient (sibling_smoothScalarTranslate a f).val x=gradient f.val (x+a) := by
  have he : fderiv ℝ (sibling_smoothScalarTranslate a f).val x=fderiv ℝ f.val (x+a) := by
    have hd := (f.property.1.differentiable (by simp) (x+a)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const a)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,sibling_smoothScalarTranslate] using hd.fderiv
  simp only [gradient,he]

lemma normalTranslateJet_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    (u : SurfaceJet (μ.map (translateNormal a))) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (normalTranslateJet μ a u).1 z=u.1 (translateNormal a z) ∧
      (normalTranslateJet μ a u).2 z=u.2 (translateNormal a z) :=
  (Lp.coeFn_compMeasurePreserving u.1 (sibling_translateNormal_measurePreserving μ a)).and
    (Lp.coeFn_compMeasurePreserving u.2 (sibling_translateNormal_measurePreserving μ a))

lemma normalTranslateJet_smooth (μ : FiniteMeasure NormalBundle) (a : Cover)
    (f : smoothPeriodicScalars) :
    normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)=
      surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f) := by
  have hscalar := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  have hgrad := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hscalar,(smoothScalarValue (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.1]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).1 (translateNormal a z)=
      f.val (translateNormal a z).1 at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).1 z=f.val ((z.1 : Cover)+(-a)) at h₂
    rw [h₁,h₂,translateNormal_periodic_eval f.property.2]
    rfl
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hgrad,(smoothScalarGradient (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.2]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).2 (translateNormal a z)=
      smoothScalarGradient f (translateNormal a z) at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).2 z=
      smoothScalarGradient (sibling_smoothScalarTranslate (-a) f) z at h₂
    rw [h₁,h₂]
    change gradient f.val (translateNormal a z).1-
      ⟪(z.2 : Cover),gradient f.val (translateNormal a z).1⟫ • (z.2 : Cover)=_
    rw [translateNormal_periodic_eval (gradient_periodic f.property.2)]
    change _=gradient (sibling_smoothScalarTranslate (-a) f).val z.1-
      ⟪(z.2 : Cover),gradient (sibling_smoothScalarTranslate (-a) f).val z.1⟫ • (z.2 : Cover)
    rw [smoothScalarTranslate_gradient]
    rfl

lemma normalTranslateJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet (μ.map (translateNormal a))} (hu : u∈surfaceH1 (μ.map (translateNormal a))) :
    normalTranslateJet μ a u∈surfaceH1 μ := by
  have hc : IsClosed ((normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) :=
    (show IsClosed (surfaceH1 μ : Set (SurfaceJet μ)) from isClosed_closure).preimage
      (normalTranslateJet μ a).continuous
  apply closure_minimal (t := (normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) ?_ hc hu
  rintro _ ⟨f,rfl⟩
  change normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)∈surfaceH1 μ
  rw [normalTranslateJet_smooth]
  exact subset_closure (LinearMap.mem_range_self _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslate_multiplier (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u : Lp ℝ 2 (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)=
      surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u) := by
  apply Lp.ext
  have hm := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    (Lp.coeFn_lpSMul (r := 2) q' u)
  filter_upwards [Lp.coeFn_compMeasurePreserving (surfaceMultiplier _ q' u)
    (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_compMeasurePreserving u (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_lpSMul (r := 2) q (normalTranslatePullback μ a ℝ u),hm,hq] with z hz hu hv hm hq
  change (normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)) z=_ at hz
  change (normalTranslatePullback μ a ℝ u) z=_ at hu
  change (surfaceMultiplier _ q (normalTranslatePullback μ a ℝ u)) z=_ at hv
  change (surfaceMultiplier _ q' u) (translateNormal a z)=_ at hm
  rw [hz]
  simp only [Function.comp_apply]
  rw [hm,hv]
  simp only [smul_eq_mul,Pi.mul_apply,hq,hu,Function.comp_apply]

lemma normalTranslate_Jacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u v : SurfaceJet (μ.map (translateNormal a))) :
    surfaceJacobiB μ q (normalTranslateJet μ a u) (normalTranslateJet μ a v)=
      surfaceJacobiB (μ.map (translateNormal a)) q' u v := by
  change ⟪normalTranslatePullback μ a Cover u.2,normalTranslatePullback μ a Cover v.2⟫-
    ⟪surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u.1),
      normalTranslatePullback μ a ℝ v.1⟫=_
  rw [← normalTranslate_multiplier μ a q q' hq u.1,
    (normalTranslatePullback μ a Cover).inner_map_map,
    (normalTranslatePullback μ a ℝ).inner_map_map]
  rfl

lemma normalTranslateField_fderiv (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (x : Cover) :
    fderiv ℝ (normalTranslateField a N) x=fderiv ℝ N (x+a) := by
  have hd := (hN.differentiable (by simp) (x+a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const a)
  change fderiv ℝ (fun y : Cover ↦ N (y+a)) x=_
  simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hd.fderiv

lemma normalTranslate_curvature (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
        (normalTranslateField_smooth a hN) (translateNormal a z)=surfaceCurvatureLp μ N hN z := by
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq' := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous (normalTranslateField_smooth a hN)).comp
      (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ.map (translateNormal a) : Measure NormalBundle)
  have he := ae_of_ae_map (measurable_translateNormal a).aemeasurable hq'
  filter_upwards [hq,he] with z hz hz'
  change surfaceCurvatureLp μ N hN z=_ at hz
  change surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
    (normalTranslateField_smooth a hN) (translateNormal a z)=_ at hz'
  rw [hz,hz']
  change coverTrace ((fderiv ℝ (normalTranslateField a N) (translateNormal a z).1).comp
    (fderiv ℝ (normalTranslateField a N) (translateNormal a z).1))=
    coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  have hper := fderiv_periodic (normalTranslateField_periodic a hp)
  rw [translateNormal_periodic_eval hper,normalTranslateField_fderiv a hN]
  simp only [sub_add_cancel]

lemma normalTranslate_smooth_inverse (a : Cover) (f : smoothPeriodicScalars) :
    sibling_smoothScalarTranslate (-a) (sibling_smoothScalarTranslate a f)=f := by
  apply Subtype.ext
  funext x
  simp only [sibling_smoothScalarTranslate,neg_add_cancel_right]

lemma normalTranslate_directional (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x) (v : Cover) :
    directionalNormalScalar (normalTranslateField a N) (normalTranslateField_smooth a hN)
      (normalTranslateField_periodic a hp) v=sibling_smoothScalarTranslate a (directionalNormalScalar N hN hp v) := by
  apply Subtype.ext
  funext x
  change _=(directionalNormalScalar N hN hp v).val (x+a)
  rw [directionalNormalScalar_apply,directionalNormalScalar_apply]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslateJet_isometry (μ : FiniteMeasure NormalBundle) (a : Cover) :
    Isometry (normalTranslateJet μ a) := by
  apply AddMonoidHomClass.isometry_of_norm (normalTranslateJet μ a)
  intro u
  change max ‖normalTranslatePullback μ a ℝ u.1‖ ‖normalTranslatePullback μ a Cover u.2‖=
    max ‖u.1‖ ‖u.2‖
  rw [(normalTranslatePullback μ a ℝ).norm_map,(normalTranslatePullback μ a Cover).norm_map]

lemma normalTranslateJet_surjective_H1 (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ u' : SurfaceJet (μ.map (translateNormal a)),u'∈surfaceH1 (μ.map (translateNormal a)) ∧
      normalTranslateJet μ a u'=u := by
  have hc : IsClosed ((normalTranslateJet μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) :=
    (normalTranslateJet_isometry μ a).isClosedEmbedding.isClosedMap _ isClosed_closure
  apply closure_minimal (t := (normalTranslateJet μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) ?_ hc hu
  rintro _ ⟨f,rfl⟩
  refine ⟨surfaceSmoothJet (μ.map (translateNormal a)) (sibling_smoothScalarTranslate a f),
    subset_closure (LinearMap.mem_range_self _ _),?_⟩
  rw [normalTranslateJet_smooth,normalTranslate_smooth_inverse]

lemma sibling_normalProjection_translate (a : Cover) (z : NormalBundle) :
    normalProjection (translateNormal a z)+quotientMap a=normalProjection z := by
  change quotientMap (representative (quotientMap z.1-quotientMap a))+quotientMap a=quotientMap z.1
  rw [quotientMap_representative,sub_add_cancel]

lemma normalTranslateField_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂(μ.map (translateNormal a) : Measure NormalBundle),
      normalTranslateField a N z.1=(z.2 : Cover) := by
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun ((hN.comp (continuous_id.add continuous_const)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change normalTranslateField a N (translateNormal a z).1=(z.2 : Cover)
  rw [translateNormal_periodic_eval (normalTranslateField_periodic a hp)]
  simpa only [normalTranslateField,sub_add_cancel] using hz

lemma normalTranslateJet_scalar_representative (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} {u' : SurfaceJet (μ.map (translateNormal a))}
    (he : normalTranslateJet μ a u'=u) {F : Torus → ℝ} (hF : Measurable F)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z)) :
    ∀ᵐ z ∂(μ.map (translateNormal a) : Measure NormalBundle),
      u'.1 z=F (normalProjection z+quotientMap a) := by
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable u'.1).measurable
      (hF.comp (normalProjection_continuous.measurable.add measurable_const)))).mpr
  filter_upwards [normalTranslateJet_ae μ a u',hae] with z hz hf
  rw [he] at hz
  change u'.1 (translateNormal a z)=F (normalProjection (translateNormal a z)+quotientMap a)
  rw [← hz.1,hf,sibling_normalProjection_translate]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarTranslate_descent (a : Cover) (f : smoothPeriodicScalars) (b : Torus) :
    (sibling_smoothScalarTranslate a f).val (representative b)=
      f.val (representative (b+quotientMap a)) := by
  have h := periodic_representative f.property.2 (representative b+a)
  rw [quotientMap_add,quotientMap_representative] at h
  exact h.symm

lemma positiveNodalPiece_translation (a : Cover) (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    IsPositiveNodalPiece (sibling_smoothScalarTranslate a f)
      ((fun b ↦ b+quotientMap a) ⁻¹' S) ((fun b ↦ b+quotientMap a) ⁻¹' D) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  constructor
  · refine ⟨(fun b ↦ b+quotientMap a) ⁻¹' U,hU.preimage (continuous_id.add continuous_const),?_⟩
    ext b
    simp only [mem_preimage,hDU,mem_inter_iff,mem_ofPred_eq,smoothScalarTranslate_descent]
  · refine ⟨(fun b ↦ b+quotientMap a) ⁻¹' C,hC.preimage (continuous_id.add continuous_const),?_⟩
    ext b
    simp only [mem_preimage,hDC,mem_inter_iff,mem_ofPred_eq,smoothScalarTranslate_descent]

lemma normalTranslate_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    {u : SurfaceJet μ} (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {u' : SurfaceJet (μ.map (translateNormal a))} (he : normalTranslateJet μ a u'=u) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN)) u' v=0 := by
  intro v hv
  rw [← normalTranslate_Jacobi μ a _ _ (normalTranslate_curvature μ a hN hp),he]
  exact hju _ (normalTranslateJet_mem_surfaceH1 μ a hv)

lemma normalTranslate_smooth_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (f : smoothPeriodicScalars)
    (hj : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN))
      (surfaceSmoothJet _ (sibling_smoothScalarTranslate a f)) v=0 := by
  apply normalTranslate_weakJacobi μ a hN hp hj
  rw [normalTranslateJet_smooth,normalTranslate_smooth_inverse]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FirstAxisShift
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

theorem isMinimizerAt_nodal_truncation_impossible_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z))
    {D : Set Torus} (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    {x : Torus} (hcl : x∈closure D) (hnot : x∉D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*f.val (representative a))
    (hFzero : ∀ a∈frontier (openRepresentative E),f.val (representative a)≤0 → F a=0) : False := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let D' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' D
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let F' : Torus → ℝ := fun b ↦ F (b+quotientMap a)
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hxS : x∈frontier (openRepresentative E) :=
    isClosed_frontier.closure_subset_iff.mpr (positiveNodalPiece_subset f hD) hcl
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  obtain ⟨u',hu',he⟩ := normalTranslateJet_surjective_H1 μ a hu
  have hD' : IsPositiveNodalPiece f' (frontier (openRepresentative E')) D' := by
    rw [hS']
    exact positiveNodalPiece_translation a f hD
  have hcl' : quotientMap cubeCenter∈closure D' := by
    change quotientMap cubeCenter∈closure ((Homeomorph.addRight (quotientMap a)) ⁻¹' D)
    rw [← (Homeomorph.addRight (quotientMap a)).preimage_closure]
    change quotientMap cubeCenter+quotientMap a∈closure D
    rwa [hshift]
  have hn' : quotientMap cubeCenter∉D' := by
    change quotientMap cubeCenter+quotientMap a∉D
    rwa [hshift]
  refine c.nodal_truncation_impossible hE' hμ' hN' hp' haeN'
    (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) ?_
    hu' (normalTranslate_weakJacobi μ a hN hp hju he)
    (hFm.comp (measurable_id.add measurable_const)) ?_
    (normalTranslateJet_scalar_representative μ a he hFm haeF) hD' hcl' hn' hk ?_ ?_
  · change ∀ v∈surfaceH1 μ',surfaceJacobiB μ' (surfaceCurvatureLp μ' N' hN')
      (surfaceSmoothJet μ' (directionalNormalScalar N' hN' hp' c.n)) v=0
    rw [normalTranslate_directional a hN hp]
    exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)
  · change ContinuousOn F' (frontier (openRepresentative E'))
    rw [hS']
    exact hF.comp (continuous_id.add continuous_const).continuousOn (fun _ h ↦ h)
  · intro b hb
    change F (b+quotientMap a)=k*(sibling_smoothScalarTranslate a f).val (representative b)
    rw [smoothScalarTranslate_descent]
    exact hFD _ hb
  · intro b hb hle
    apply hFzero
    · rwa [hS'] at hb
    · rwa [smoothScalarTranslate_descent] at hle

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible_oai := @OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible_oai
