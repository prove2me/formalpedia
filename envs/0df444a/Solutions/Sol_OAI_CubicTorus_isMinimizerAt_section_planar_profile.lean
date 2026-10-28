-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_section_planar_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:26:56.851181+00:00
-- url     : https://prove2.me/submissions/55fcb27f-0ec2-460b-bd75-5c75d52f08fd

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_extent_perimeter
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_strip_perimeter
import Theorems.Thm_OAI_CubicTorus_planar_radial_isoperimetric

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

theorem integral_divergence_fundamentalCube {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, divergence F x) = 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (1 : Fin 3 → ℝ) (by intro i; norm_num)
    g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : (∑ i : Fin 3,
      ((∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 1 x)) -
       ∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 0 x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth 1 x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  have hi : (∫ x in Icc (0 : Fin 3 → ℝ) 1, divergence F (e.symm x)) = 0 := hth.trans hzero
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, cube_preimage]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  exact hi

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma integral_divergence_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Eᶜ, divergence F x) =
      -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hi := integral_add_compl₀ hm (integrableOn_divergence hF.1)
  rw [Measure.restrict_restrict₀ hm, Measure.restrict_restrict₀ hm.compl,
    integral_divergence_fundamentalCube hF] at hi
  simp only [inter_comm] at hi
  rw [preimage_compl]
  linarith

theorem perimeter_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter Eᶜ = perimeter E := by
  have hle : ∀ E : Set Torus, NullMeasurableSet E torusVolume →
      perimeter Eᶜ ≤ perimeter E := by
    intro E hE
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun x => -F x)
    apply le_iSup_of_le (admissible_neg hF)
    rw [integral_divergence_compl hE hF]
    simp only [divergence_neg, integral_neg, le_refl]
  exact le_antisymm (hle E hE) (by simpa only [compl_compl] using hle Eᶜ hE.compl)

theorem finitePerimeter_compl {E : Set Torus} :
    FinitePerimeter Eᶜ ↔ FinitePerimeter E := by
  constructor
  · rintro ⟨hm, hp⟩
    have hm' : NullMeasurableSet E torusVolume := by simpa using hm.compl
    exact ⟨hm', by simpa only [perimeter_compl hm'] using hp⟩
  · rintro ⟨hm, hp⟩
    exact ⟨hm.compl, by rwa [perimeter_compl hm]⟩

lemma volume_compl_of_volume {E : Set Torus} {V : ℝ}
    (hE : NullMeasurableSet E torusVolume) (hV : 0 ≤ V)
    (hvolume : torusVolume E = ENNReal.ofReal V) :
    torusVolume Eᶜ = ENNReal.ofReal (1 - V) := by
  rw [measure_compl₀ hE (measure_ne_top _ _), torusVolume_univ, hvolume,
    ENNReal.ofReal_sub 1 hV, ENNReal.ofReal_one]

theorem isMinimizerAt_compl {V : ℝ} (hV : V ∈ Icc 0 1) {E : Set Torus} :
    IsMinimizerAt (1 - V) Eᶜ ↔ IsMinimizerAt V E := by
  have hforward : ∀ V : ℝ, V ∈ Icc 0 1 → ∀ E : Set Torus,
      IsMinimizerAt V E → IsMinimizerAt (1 - V) Eᶜ := by
    intro V hV E ⟨hE, hvolume, hmin⟩
    refine ⟨finitePerimeter_compl.mpr hE, volume_compl_of_volume hE.1 hV.1 hvolume, ?_⟩
    intro F hF hFvolume
    have hFcvolume : torusVolume Fᶜ = ENNReal.ofReal V := by
      have hh := volume_compl_of_volume hF.1 (sub_nonneg.mpr hV.2) hFvolume
      simpa only [sub_sub_cancel] using hh
    have hm := hmin Fᶜ (finitePerimeter_compl.mpr hF) hFcvolume
    rwa [perimeter_compl hE.1, perimeter_compl hF.1] at *
  constructor
  · intro h
    have hv : 1 - V ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hV.2, by linarith [hV.1]⟩
    simpa only [sub_sub_cancel, compl_compl] using hforward (1 - V) hv Eᶜ h
  · exact hforward V hV E

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

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

end CubicTorus

end
end

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

lemma sibling_coverCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Cover) (i : Fin 3) :
    sibling_coverCoordinatePermute e x i=x (e i) := by
  rfl

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

lemma axisReflection_cover_apply (i j : Fin 3) (x : Cover) :
    (axisReflection i).cover x j=if j=i then -x j else x j := by
  classical
  change (sibling_coverCoordinatePermute (Equiv.swap 0 i)
    (firstReflection (sibling_coverCoordinatePermute (Equiv.swap 0 i) x))) j=_
  simp only [sibling_coverCoordinatePermute_apply,firstReflection_apply,Equiv.swap_apply_self]
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

lemma octantContract_apply (t : ℝ) (x : Cover) (i : Fin 3) :
    octantContract t x i=(1-t)*x i+t*(3/4 : ℝ) := rfl

lemma octantContract_mem {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1)
    {x : Cover} (hx : x∈closedUpperOctant) : octantContract t x∈upperOctant := by
  intro i
  rw [octantContract_apply]
  have h1 := mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr (hx i).1)
  have h2 := mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith [ht.1]

lemma octantContract_mono {t : ℝ} (ht : t≤1) {b : Fin 3 → Bool} {x y : Cover}
    (hxy : OrientedCoordinateLE b x y) :
    OrientedCoordinateLE b (octantContract t x) (octantContract t y) := by
  intro i
  simp only [octantContract_apply]
  have hh := hxy i
  cases hbi : b i <;> simp only [hbi,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · linarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]
  · linarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]

lemma octantContract_tendsto (x : Cover) :
    Tendsto (fun t : ℝ ↦ quotientMap (octantContract t x)) (𝓝[>]0) (𝓝 (quotientMap x)) := by
  have hc : Continuous (fun t : ℝ ↦ quotientMap (octantContract t x)) := by
    exact continuous_quotientMap.comp
      (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const))
  have hh := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [octantContract] using hh

lemma octant_downset_closed_endpoint {O : Set Torus} (hO : IsOpen O)
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈O → quotientMap x∈O)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyo : quotientMap y∈O) :
    quotientMap x∈closure O := by
  have hyv : ∀ᶠ t in 𝓝[>](0 : ℝ),quotientMap (octantContract t y)∈O :=
    octantContract_tendsto y (hO.mem_nhds hyo)
  apply isClosed_closure.mem_of_tendsto (octantContract_tendsto x)
  filter_upwards [hyv,self_mem_nhdsWithin,(eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with t hty ht0 ht1
  exact subset_closure (hd _ (octantContract_mem ⟨ht0,ht1⟩ hx)
    _ (octantContract_mem ⟨ht0,ht1⟩ hy) (octantContract_mono ht1.le hxy) hty)

end CubicTorus

end
end

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

lemma octantFlipSet_empty (x : Cover) : octantFlipSet ∅ x=x := by
  ext i; simp [octantFlipSet]

lemma octantFlipSet_insert {s : Finset (Fin 3)} {i : Fin 3} (hi : i∉s) (x : Cover) :
    octantFlipSet (insert i s) x=(axisReflection i).cover (octantFlipSet s x)+
      latticeVector (Pi.single i (1 : ℤ)) := by
  ext j
  rw [PiLp.add_apply,axisReflection_cover_apply]
  by_cases hji : j=i
  · subst j
    simp [octantFlipSet,hi,latticeVector,Pi.single_eq_same]
    ring
  · simp [octantFlipSet,hji,latticeVector,Pi.single_apply]

lemma octantFlipSet_mem {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (s : Finset (Fin 3)) (x : Cover) : quotientMap (octantFlipSet s x)∈O ↔ quotientMap x∈O := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [octantFlipSet_empty]
  | @insert i s hi ih =>
    rw [octantFlipSet_insert hi,quotientMap_add,quotientMap_latticeVector,add_zero,
      (axisReflection i).commute,hR,ih]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_closure_openRepresentative_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E)=volumeSupport E := by
  let F := toMeasurable torusVolume E
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  rw [←openRepresentative_congr_ae hFE,←volumeSupport_congr_ae hFE]
  exact isMinimizerAt_closure_openRepresentative hV (measurableSet_toMeasurable _ _)
    ((isMinimizerAt_congr_ae hFE).mpr hmin)

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

lemma upperFold_continuous : Continuous upperFold := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i ↦ continuous_const.sub ((PiLp.continuous_apply 2 _ i).norm)))

lemma upperFold_mem (z : Torus) : upperFold z∈closedUpperOctant := by
  intro i
  have hh := AddCircle.norm_le_half_period 1 (x := z i) (by norm_num)
  norm_num at hh
  change (1/2 : ℝ)≤1-‖z i‖ ∧ 1-‖z i‖≤1
  constructor <;> linarith [norm_nonneg (z i)]

lemma circle_norm_upper {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1) :
    ‖(t : AddCircle (1 : ℝ))‖=1-t := by
  have he : ((t-1 : ℝ) : AddCircle (1 : ℝ))=(t : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub,AddCircle.coe_period,sub_zero]
  have hh := (AddCircle.norm_coe_eq_abs_iff 1 (x := t-1) (by norm_num)).mpr (by
    rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)]
    norm_num
    linarith [ht.1])
  rw [he,abs_of_nonpos (by linarith [ht.2] : t-1≤0)] at hh
  linarith

lemma upperFold_quotient {x : Cover} (hx : x∈closedUpperOctant) :
    upperFold (quotientMap x)=x := by
  ext i
  change 1-‖(x i : AddCircle (1 : ℝ))‖=x i
  rw [circle_norm_upper (hx i)]
  ring

lemma upperFold_eq_flip (z : Torus) : upperFold z=
    octantFlipSet (Finset.univ.filter (fun i ↦ representative z i≤1/2)) (representative z) := by
  classical
  have hz := quotientMap_representative z
  ext i
  have he : ((representative z i : ℝ) : AddCircle (1 : ℝ))=z i := congrArg (fun z : Torus ↦ z i) hz
  have hr := representative_mem_fundamentalCube z i
  change 0 ≤ representative z i ∧ representative z i<1 at hr
  change 1-‖z i‖=if i∈Finset.univ.filter (fun j ↦ representative z j≤1/2) then 1-representative z i else representative z i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : representative z i≤1/2
  · rw [ite_eq_left hi,←he]
    have hh := (AddCircle.norm_coe_eq_abs_iff 1 (x := representative z i) (by norm_num)).mpr (by
      rw [abs_of_nonneg hr.1]; norm_num; exact hi)
    rw [hh,abs_of_nonneg hr.1]
  · rw [ite_eq_right hi,←he,circle_norm_upper ⟨(not_le.mp hi).le,hr.2.le⟩]
    ring

lemma upperFold_phase {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (z : Torus) : quotientMap (upperFold z)∈O ↔ z∈O := by
  rw [upperFold_eq_flip,octantFlipSet_mem hR,quotientMap_representative]

theorem octant_downset_closure {O : Set Torus} (hO : IsOpen O)
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈O → quotientMap x∈O)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyO : quotientMap y∈closure O) :
    quotientMap x∈closure O := by
  let f : Torus → Cover := fun z ↦ WithLp.toLp 2 (fun i ↦
    if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))
  have hfc : Continuous (fun z ↦ quotientMap (f z)) := by
    apply continuous_quotientMap.comp
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    have hu := (PiLp.continuous_apply 2 _ i).comp upperFold_continuous
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
      first | exact continuous_const.max hu | exact continuous_const.min hu
  have hfmem (z : Torus) : f z∈closedUpperOctant := by
    intro i
    have hh := upperFold_mem z i
    change (1/2 : ℝ)≤(if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i)) ∧
      (if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))≤1
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨(hx i).1.trans (le_max_left _ _),max_le (hx i).2 hh.2⟩
    · exact ⟨le_min (hx i).1 hh.1,(min_le_left _ _).trans (hx i).2⟩
  have hford (z : Torus) : OrientedCoordinateLE b (f z) (upperFold z) := by
    intro i
    change if b i then (if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))≤upperFold z i
      else upperFold z i≤(if b i then min (x i) (upperFold z i) else max (x i) (upperFold z i))
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact le_max_right _ _
    · exact min_le_right _ _
  have hclosure : closure O⊆(fun z ↦ quotientMap (f z)) ⁻¹' closure O := by
    apply closure_minimal _ (isClosed_closure.preimage hfc)
    intro z hz
    exact octant_downset_closed_endpoint hO hd (hfmem z) (upperFold_mem z) (hford z)
      ((upperFold_phase hR z).mpr hz)
  have he : f (quotientMap y)=x := by
    ext i
    change (if b i then min (x i) (upperFold (quotientMap y) i) else max (x i) (upperFold (quotientMap y) i))=x i
    rw [upperFold_quotient hy]
    have hh := hxy i
    cases h : b i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    · exact max_eq_left hh
    · exact min_eq_left hh
  simpa only [mem_preimage,he] using hclosure hyO

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma orientedCoordinateLE_reverse (b : Fin 3 → Bool) (x y : Cover) :
    OrientedCoordinateLE (fun i ↦ !b i) x y ↔ OrientedCoordinateLE b y x := by
  constructor <;> intro h i <;> have hh := h i <;> cases hb : b i <;>
    simpa only [hb,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using hh

theorem isMinimizerAt_closed_octant_order {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyO : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
  have hcl := isMinimizerAt_closure_openRepresentative_null hV hmin
  have hclc := isMinimizerAt_closure_openRepresentative_null hVc hmc
  have hdcomp : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE (fun i ↦ !b i) x y →
      quotientMap y∈openRepresentative Eᶜ →quotientMap x∈openRepresentative Eᶜ := by
    intro u hu v hv huv hvO
    simp only [openRepresentative,compl_compl,mem_compl_iff] at hvO ⊢
    intro hucl
    have hur : u∈closedUpperOctant := fun i ↦ ⟨(hu i).1.le,(hu i).2.le⟩
    have hvr : v∈closedUpperOctant := fun i ↦ ⟨(hv i).1.le,(hv i).2.le⟩
    have hh := octant_downset_closure (isOpen_openRepresentative E)
      (reflection_invariant_openRepresentative hmin.1.1 hR) hd hvr hur
      ((orientedCoordinateLE_reverse b u v).mp huv) (by rwa [hcl])
    rw [hcl] at hh
    exact hvO (by simpa only [compl_compl] using hh)
  by_contra hxo
  have hxcl : quotientMap x∈closure (openRepresentative Eᶜ) := by
    rw [hclc]
    simpa only [openRepresentative,mem_compl_iff,not_not] using hxo
  have hh := octant_downset_closure (isOpen_openRepresentative Eᶜ)
    (reflection_invariant_openRepresentative hmc.1.1 hRc) hdcomp hy hx
    ((orientedCoordinateLE_reverse b y x).mpr hxy) hxcl
  rw [hclc] at hh
  exact hyO hh

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

lemma torusAxialSplit_measurePreserving (i : Fin 3) :
    MeasurePreserving (torusAxialSplit i) torusVolume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i).comp
    torus_to_product_measurePreserving

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma upperFold_slice_succAbove (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) (j : Fin 2) :
    upperFold ((torusAxialSplit i).symm (t,y)) (i.succAbove j)=1-‖y j‖ := by
  change 1-‖((torusAxialSplit i).symm (t,y)) (i.succAbove j)‖=1-‖y j‖
  rw [torusAxialSplit_symm_succAbove]

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

lemma axialSliceIntegral_pairing {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    {f : Torus → ℝ} (hf : Continuous f) {ψ : AxisCircle → ℝ} (hψ : Continuous ψ) :
    (∫ t,ψ t*axialSliceIntegral E i f t)=∫ z in E,ψ (z i)*f z ∂torusVolume := by
  have hi : Integrable (fun z : Torus ↦ ψ (z i)*f z) torusVolume :=
    ((hψ.comp (PiLp.continuous_apply 2 _ i)).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := (torusAxialSplit_measurePreserving i).symm.integrable_comp_of_integrable (hi.indicator hE)
  rw [←integral_indicator hE,←(torusAxialSplit_measurePreserving i).symm.integral_comp'
    (E.indicator (fun z : Torus ↦ ψ (z i)*f z))]
  change _=∫ z,((E.indicator (fun z : Torus ↦ ψ (z i)*f z)) ∘ (torusAxialSplit i).symm) z ∂volume.prod volume
  rw [integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [axialSliceIntegral_indicator hE,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : (torusAxialSplit i).symm (t,y)∈E <;> simp [hy]

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

lemma planeAxisProjection_representative (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    planeAxisProjection i (representative ((torusAxialSplit i).symm (t,y)))=planarRepresentative y := by
  ext j
  simp [representative,planarRepresentative]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCorner
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

lemma torusAxialSplit_symm_continuous (i : Fin 3) :
    Continuous (torusAxialSplit i).symm := by
  change Continuous (fun p : AxisCircle × TransverseProduct ↦ WithLp.toLp 2 (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) p.1 p.2))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (Fin.forall_iff_succAbove (P := fun j : Fin 3 ↦ Continuous
    (fun p : AxisCircle × TransverseProduct ↦ (i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) p.1 p.2) j)) i).mpr
    ⟨by simp only [Fin.insertNth_apply_same]; exact continuous_fst,
      fun k ↦ by simp only [Fin.insertNth_apply_succAbove]; exact (continuous_apply k).comp continuous_snd⟩ j

lemma axialSlice_isOpen {O : Set Torus} (hO : IsOpen O) (i : Fin 3) (t : AxisCircle) :
    IsOpen (axialSlice O i t) :=
  hO.preimage ((torusAxialSplit_symm_continuous i).comp (continuous_const.prodMk continuous_id))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarRadialDownset
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

lemma axisCircle_norm_le_half (z : AxisCircle) : ‖z‖≤1/2 := by
  simpa using AddCircle.norm_le_half_period 1 (x := z) (by norm_num)

lemma axisCircle_norm_coe_small {t : ℝ} (ht : |t|≤1/2) : ‖(t : AxisCircle)‖=|t| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_exists_centered_rep (z : AxisCircle) :
    ∃ t : ℝ,(t : AxisCircle)=z ∧ |t|=‖z‖ := by
  let t := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z : ℝ)
  have ht := (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) z).property
  have hbound : |t|≤1/2 := abs_le.mpr ⟨ht.1,by dsimp [t]; linarith [ht.2]⟩
  have he : (t : AxisCircle)=z := AddCircle.coe_equivIco
  exact ⟨t,he,by rw [←he,axisCircle_norm_coe_small hbound]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_same_quotient_lattice {x y : Plane} (h : planarQuotient x=planarQuotient y) :
    ∃ n : Fin 2 →ℤ,x=y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)) := by
  have hh : ∀ j : Fin 2,∃ n : ℤ,(n : ℝ)=x j-y j := by
    intro j
    have hi : ((x j-y j : ℝ) : AxisCircle)=0 := by
      have he := congrFun h j
      simpa only [planarQuotient,AddCircle.coe_sub] using sub_eq_zero.mpr he
    simpa only [zsmul_eq_mul,mul_one] using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi)
  choose n hn using hh
  refine ⟨n,?_⟩
  ext j
  change x j=y j+(n j : ℝ)
  linarith [hn j]

lemma planeDivergence_translate (F : Plane →Plane) (a y : Plane) :
    planeDivergence (fun z ↦ F (z+a)) y=planeDivergence F (y+a) := by
  simp only [planeDivergence,fderiv_comp_add_right]

lemma planeDivergence_periodic {F : Plane →Plane}
    (hF : ∀ (n : Fin 2 →ℤ) y,F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=F y)
    (n : Fin 2 →ℤ) (y : Plane) :
    planeDivergence F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=planeDivergence F y := by
  have he : (fun y : Plane ↦ F (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ))))=F := funext (hF n)
  rw [←planeDivergence_translate,he]

lemma planarAdmissibleField_translate {F : Plane →Plane} (hF : PlanarAdmissibleField F) (a : Plane) :
    PlanarAdmissibleField (fun y ↦ F (y+a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const),?_,fun y ↦ hF.2.2 _⟩
  intro n y
  change F ((y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))+a)=F (y+a)
  rw [add_right_comm,hF.2.1]

lemma planar_flux_translation {F : Plane →Plane} (hF : PlanarAdmissibleField F)
    (a : Plane) (A : Set TransverseProduct) :
    (∫ y in (fun z : TransverseProduct ↦ z+planarQuotient a) ⁻¹' A,
      planeDivergence F (planarRepresentative y))=
    ∫ y in A,planeDivergence (fun z ↦ F (z-a)) (planarRepresentative y) := by
  have he : (fun y : TransverseProduct ↦ planeDivergence F (planarRepresentative y))=
      (fun y ↦ planeDivergence (fun z ↦ F (z-a)) (planarRepresentative (y+planarQuotient a))) := by
    funext y
    simp only [sub_eq_add_neg,planeDivergence_translate]
    have hq : planarQuotient (planarRepresentative (y+planarQuotient a)+-a)=
        planarQuotient (planarRepresentative y) := by simp
    obtain ⟨n,hn⟩ := planar_same_quotient_lattice hq
    rw [hn,planeDivergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right (volume : Measure TransverseProduct) (planarQuotient a)).setIntegral_preimage_emb
    (Homeomorph.addRight (planarQuotient a)).measurableEmbedding
    (fun y ↦ planeDivergence (fun z ↦ F (z-a)) (planarRepresentative y)) A

lemma planarTorusPerimeter_translation_le (A : Set TransverseProduct) (a : Plane) :
    planarTorusPerimeter ((fun y : TransverseProduct ↦ y+planarQuotient a) ⁻¹' A)≤planarTorusPerimeter A := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [planar_flux_translation hF a A]
  have hG : PlanarAdmissibleField (fun y ↦ F (y-a)) := by
    simpa only [sub_eq_add_neg] using planarAdmissibleField_translate hF (-a)
  exact le_iSup_of_le (fun y ↦ F (y-a)) (le_iSup_of_le hG le_rfl)

theorem planarTorusPerimeter_translation (A : Set TransverseProduct) (a : TransverseProduct) :
    planarTorusPerimeter ((fun y : TransverseProduct ↦ y+a) ⁻¹' A)=planarTorusPerimeter A := by
  have ha := planarQuotient_representative a
  refine le_antisymm (by simpa only [ha] using planarTorusPerimeter_translation_le A (planarRepresentative a)) ?_
  have hh := planarTorusPerimeter_translation_le ((fun y : TransverseProduct ↦ y+a) ⁻¹' A) (-planarRepresentative a)
  have he : (fun y : TransverseProduct ↦ y+planarQuotient (-planarRepresentative a)) ⁻¹'
      ((fun y : TransverseProduct ↦ y+a) ⁻¹' A)=A := by
    ext y
    simp
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisCircle_norm_add_half (z : AxisCircle) :
    ‖z+((1/2 : ℝ) : AxisCircle)‖=1/2-‖z‖ := by
  obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep z
  have hb : |t|≤1/2 := ht.trans_le (axisCircle_norm_le_half z)
  rw [←he,←AddCircle.coe_add,axisCircle_norm_coe_small hb]
  by_cases hpos : 0≤t
  · rw [circle_norm_upper ⟨by linarith,(by linarith [(le_abs_self t).trans hb])⟩,abs_of_nonneg hpos]
    ring
  · have ht0 := le_of_not_ge hpos
    have hp : 0≤t+1/2 := by linarith [neg_le_of_abs_le hb]
    rw [axisCircle_norm_coe_small (by rw [abs_of_nonneg hp]; linarith),abs_of_nonneg hp,abs_of_nonpos ht0]
    ring

lemma upperFold_centered_slice (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle)
    (y : TransverseProduct) (j : Fin 2) :
    upperFold ((torusAxialSplit i).symm (t,y+axialSectionCenter b i)) (i.succAbove j)=
      if b (i.succAbove j) then 1/2+‖y j‖ else 1-‖y j‖ := by
  rw [upperFold_slice_succAbove]
  change 1-‖y j+(if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0)‖=_
  cases b (i.succAbove j) <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero]
  rw [axisCircle_norm_add_half]
  ring

lemma centeredAxialSlice_isOpen {O : Set Torus} (hO : IsOpen O) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    IsOpen (centeredAxialSlice O b i t) :=
  (axialSlice_isOpen hO i t).preimage (continuous_add_const _)

lemma centeredAxialSlice_closure_subset (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    closure (centeredAxialSlice O b i t)⊆centeredAxialSlice (closure O) b i t := by
  apply closure_minimal
  · exact preimage_mono (preimage_mono subset_closure)
  · exact (isClosed_closure.preimage ((torusAxialSplit_symm_continuous i).comp
      (continuous_const.prodMk (continuous_add_const (axialSectionCenter b i)))))

theorem isMinimizerAt_centered_section_radial {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : AxisCircle) :
    PlanarRadialDownset (centeredAxialSlice (openRepresentative E) b i t) := by
  intro y z hyz hz
  let Y := (torusAxialSplit i).symm (t,y+axialSectionCenter b i)
  let Z := (torusAxialSplit i).symm (t,z+axialSectionCenter b i)
  change Y∈openRepresentative E
  have hre := reflection_invariant_openRepresentative hmin.1.1 hR
  apply (upperFold_phase hre Y).mp
  apply isMinimizerAt_closed_octant_order hV hmin hR hd (upperFold_mem Y) (upperFold_mem Z) _
    ((upperFold_phase hre Z).mpr hz)
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k
    change if b i then 1-‖Y i‖≤1-‖Z i‖ else 1-‖Z i‖≤1-‖Y i‖
    simp only [Y,Z,torusAxialSplit_symm_same,le_refl,ite_self]
  · dsimp only [Y,Z]
    rw [upperFold_centered_slice,upperFold_centered_slice]
    cases b (i.succAbove j) <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [hyz j]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma centered_section_corner (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 →Bool) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarSquareCorner n+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t n) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k
    simp [quotientMap]
  · simp only [torusAxialSplit_symm_succAbove,Pi.add_apply,planarSquareCorner,axialSectionCenter]
    simp only [quotientMap,axialSectionCorner,Fin.insertNth_apply_succAbove]
    change (if n j then ((1/2 : ℝ) : AxisCircle) else 0)+
      (if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0)=
        (octantHeight b (i.succAbove j) (if n j then 1 else 0) : AxisCircle)
    cases hn : n j <;> cases hb : b (i.succAbove j) <;>
      norm_num [octantHeight,hn,hb,AddCircle.coe_period]
    rw [←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]

lemma centered_section_zero (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),(0 : TransverseProduct)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun _ ↦ false)) := by
  have he : planarSquareCorner (fun _ ↦ false)=(0 : TransverseProduct) := by ext j; simp [planarSquareCorner]
  simpa only [he] using centered_section_corner b i t (fun _ ↦ false)

lemma centered_section_first_axis (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun j ↦ j==0)) := by
  have he : planarFirstAxisPoint (1/2)=planarSquareCorner (fun j ↦ j==0) := by
    ext j; fin_cases j <;> simp [planarFirstAxisPoint,planarSquareCorner]
  rw [he,centered_section_corner]

lemma centered_section_second_axis (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) :
    (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)=
      quotientMap (axialSectionCorner b i t (fun j ↦ j==1)) := by
  have he : planarAxisPoint (1/2)=planarSquareCorner (fun j ↦ j==1) := by
    ext j; fin_cases j <;> simp [planarAxisPoint,planarSquareCorner]
  rw [he,centered_section_corner]

lemma centeredAxialSlice_volume (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    volume.real (centeredAxialSlice O b i t)=volume.real (axialSlice O i t) := by
  apply congrArg ENNReal.toReal
  exact (measurePreserving_add_right (volume : Measure TransverseProduct) (axialSectionCenter b i)).measure_preimage_emb
    (Homeomorph.addRight (axialSectionCenter b i)).measurableEmbedding _

lemma centeredAxialSlice_perimeter (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    planarTorusPerimeter (centeredAxialSlice O b i t)=planarTorusPerimeter (axialSlice O i t) :=
  planarTorusPerimeter_translation _ _

theorem isMinimizerAt_section_disk_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
    ENNReal.ofReal (2*Real.sqrt (Real.pi*volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hzero : (0 : TransverseProduct)∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle) := by
    change (torusAxialSplit i).symm ((t : AxisCircle),0+axialSectionCenter b i)∈openRepresentative E
    rwa [centered_section_zero]
  have hv0 : planarFirstAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_first_axis] at hz
    exact hout0 hz
  have hv1 : planarAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_second_axis] at hz
    exact hout1 hz
  have hp := planar_radial_isoperimetric (centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _)
    (isMinimizerAt_centered_section_radial hV hmin hR hd i _) hzero hv0 hv1
  simpa only [centeredAxialSlice_volume,centeredAxialSlice_perimeter] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_descended_divergence_continuous {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    Continuous (fun y : TransverseProduct ↦ planeDivergence F (planarRepresentative y)) := by
  have hLF := liftPlanarField_admissible (0 : Fin 3) hF
  have hc := continuous_periodic_descent (continuous_divergence hLF.1) (divergence_periodic hLF.2.1)
  have hh := hc.comp ((torusAxialSplit_symm_continuous 0).comp
    ((continuous_const : Continuous (fun _ : TransverseProduct ↦ (0 : AxisCircle))).prodMk (continuous_id : Continuous (fun y : TransverseProduct ↦ y))))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  dsimp only [Function.comp_apply,id_eq]
  rw [divergence_liftPlanarField 0 hF.1,planeAxisProjection_representative]

lemma planar_integral_divergence_zero {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    (∫ y : TransverseProduct,planeDivergence F (planarRepresentative y))=0 := by
  have hLF := liftPlanarField_admissible (0 : Fin 3) hF
  have hc := continuous_periodic_descent (continuous_divergence hLF.1) (divergence_periodic hLF.2.1)
  have hz : (∫ z : Torus,divergence (liftPlanarField 0 F) (representative z) ∂torusVolume)=0 := by
    have hh := setIntegral_lift (continuous_divergence hLF.1) (divergence_periodic hLF.2.1) (E := univ) MeasurableSet.univ
    simpa only [setIntegral_univ,preimage_univ,inter_univ,integral_divergence_fundamentalCube hLF] using hh
  have hh := axialSliceIntegral_pairing (E := univ) MeasurableSet.univ (0 : Fin 3) hc
    (ψ := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [one_mul,setIntegral_univ] at hh
  rw [hz] at hh
  simp only [axialSliceIntegral,axialSlice,mem_univ,ofPred_true,
    divergence_liftPlanarField 0 hF.1,planeAxisProjection_representative,setIntegral_univ] at hh
  simpa using hh

lemma planarAdmissibleField_neg {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    PlanarAdmissibleField (fun y ↦ -F y) := by
  refine ⟨hF.1.neg,fun n y ↦ congrArg Neg.neg (hF.2.1 n y),?_⟩
  intro y
  simpa only [norm_neg] using hF.2.2 y

lemma planeDivergence_neg (F : Plane →Plane) (y : Plane) :
    planeDivergence (fun z ↦ -F z) y=-planeDivergence F y := by
  simp [planeDivergence]
  ring

lemma planar_integral_divergence_compl {A : Set TransverseProduct} (hA : NullMeasurableSet A volume)
    {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    (∫ y in Aᶜ,planeDivergence F (planarRepresentative y))=
      -(∫ y in A,planeDivergence F (planarRepresentative y)) := by
  have hi := integral_add_compl₀ hA
    ((planar_descended_divergence_continuous hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [planar_integral_divergence_zero hF] at hi
  linarith

theorem planarTorusPerimeter_compl {A : Set TransverseProduct} (hA : NullMeasurableSet A volume) :
    planarTorusPerimeter Aᶜ=planarTorusPerimeter A := by
  have hle : ∀ B : Set TransverseProduct,NullMeasurableSet B volume →
      planarTorusPerimeter Bᶜ≤planarTorusPerimeter B := by
    intro B hB
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun y ↦ -F y)
    apply le_iSup_of_le (planarAdmissibleField_neg hF)
    rw [planar_integral_divergence_compl hB hF]
    simp only [planeDivergence_neg,integral_neg,le_refl]
  exact le_antisymm (hle A hA) (by simpa only [compl_compl] using hle Aᶜ hA.compl)

lemma planarTorusPerimeter_congr_ae {A B : Set TransverseProduct} (h : A=ᵐ[volume]B) :
    planarTorusPerimeter A=planarTorusPerimeter B := by
  unfold planarTorusPerimeter
  congr 1
  funext F
  congr 1
  funext hF
  rw [setIntegral_congr_set h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_complement_octant_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) :
    ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE (fun i ↦ !b i) x y →
      quotientMap y∈openRepresentative Eᶜ →quotientMap x∈openRepresentative Eᶜ := by
  have hcl := isMinimizerAt_closure_openRepresentative_null hV hmin
  intro u hu v hv huv hvO
  simp only [openRepresentative,compl_compl,mem_compl_iff] at hvO ⊢
  intro hucl
  have hur : u∈closedUpperOctant := fun i ↦ ⟨(hu i).1.le,(hu i).2.le⟩
  have hvr : v∈closedUpperOctant := fun i ↦ ⟨(hv i).1.le,(hv i).2.le⟩
  have hh := octant_downset_closure (isOpen_openRepresentative E)
    (reflection_invariant_openRepresentative hmin.1.1 hR) hd hvr hur
    ((orientedCoordinateLE_reverse b u v).mp huv) (by rwa [hcl])
  rw [hcl] at hh
  exact hvO (by simpa only [compl_compl] using hh)

lemma axialSectionCorner_reverse (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 →Bool) :
    axialSectionCorner (fun k ↦ !b k) i t n=axialSectionCorner b i t (fun j ↦ !n j) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨j,rfl⟩
  · subst k; simp [axialSectionCorner]
  · simp only [axialSectionCorner,Fin.insertNth_apply_succAbove]
    dsimp only [octantHeight]
    by_cases hn : n j=true <;> by_cases hb : b (i.succAbove j)=true <;> norm_num [hn,hb]

lemma openRepresentative_compl_eq {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    openRepresentative Eᶜ=(closure (openRepresentative E))ᶜ := by
  rw [isMinimizerAt_closure_openRepresentative_null hV hmin]
  simp only [openRepresentative,compl_compl]

lemma closure_openRepresentative_compl_eq {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    closure (openRepresentative Eᶜ)=(openRepresentative E)ᶜ := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  rw [isMinimizerAt_closure_openRepresentative_null hVc ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin)]
  simp only [openRepresentative,compl_compl]

lemma axialSlice_openRepresentative_compl_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    axialSlice (openRepresentative Eᶜ) i t=ᵐ[volume]((axialSlice (openRepresentative E) i t)ᶜ : Set TransverseProduct) := by
  have hnb : ∀ᵐ y : TransverseProduct,y∉axialSlice (frontier (openRepresentative E)) i t := by
    rw [ae_iff]
    convert hn using 2
    all_goals try with_reducible_and_instances rfl
    ext y
    simp
  filter_upwards [hnb] with y hy
  rw [openRepresentative_compl_eq hV hmin]
  apply propext
  change ((torusAxialSplit i).symm (t,y)∉closure (openRepresentative E)) ↔
    (torusAxialSplit i).symm (t,y)∉openRepresentative E
  constructor
  · intro h hc; exact h (subset_closure hc)
  · intro h hc
    apply hy
    change (torusAxialSplit i).symm (t,y)∈frontier (openRepresentative E)
    rw [(isOpen_openRepresentative E).frontier_eq]
    exact ⟨hc,h⟩

lemma axialSlice_complement_volume {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    volume.real (axialSlice (openRepresentative Eᶜ) i t)=
      1-volume.real (axialSlice (openRepresentative E) i t) := by
  have hv : volume (axialSlice (openRepresentative E) i t)≤1 := by
    simpa using (measure_mono (subset_univ (axialSlice (openRepresentative E) i t)) : volume _≤volume univ)
  rw [measureReal_def,measure_congr (axialSlice_openRepresentative_compl_ae hV hmin i t hn)]
  rw [measure_compl (axialSlice_measurable (isOpen_openRepresentative E).measurableSet i t) (measure_ne_top _ _),
    measure_univ,ENNReal.toReal_sub_of_le hv ENNReal.one_ne_top,
    ENNReal.toReal_one]
  rfl

lemma axialSlice_complement_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) (t : AxisCircle)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i t)=0) :
    planarTorusPerimeter (axialSlice (openRepresentative Eᶜ) i t)=
      planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  rw [planarTorusPerimeter_congr_ae (axialSlice_openRepresentative_compl_ae hV hmin i t hn),
    planarTorusPerimeter_compl (axialSlice_measurable (isOpen_openRepresentative E).measurableSet i t).nullMeasurableSet]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_complement_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hout : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (t : AxisCircle),‖y 1‖<L) ∧
      ENNReal.ofReal ((1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) ∧
      ENNReal.ofReal (2*Real.sqrt (Real.pi*(1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
  have hdc := isMinimizerAt_complement_octant_downset hV hmin hR hd
  have hswap0 : (fun j : Fin 2 ↦ !(j==0))=(fun j ↦ j==1) := by funext j; fin_cases j <;> decide
  have hswap1 : (fun j : Fin 2 ↦ !(j==1))=(fun j ↦ j==0) := by funext j; fin_cases j <;> decide
  have hin : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun _ ↦ false))∈openRepresentative Eᶜ := by
    rw [openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse]
    exact hout
  have hv0 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==0))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap0]
    simpa using hin1
  have hv1 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==1))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap1]
    simpa using hin0
  obtain ⟨L,hL,hband,hp⟩ := isMinimizerAt_section_extent_perimeter hVc hmc hRc hdc i t hin hv0 hv1
  have hh := isMinimizerAt_section_disk_perimeter hVc hmc hRc hdc i t hin hv0 hv1
  rw [axialSlice_complement_volume hV hmin i _ hn,axialSlice_complement_perimeter hV hmin i _ hn] at hp hh
  exact ⟨L,hL,hband,hp,hh⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
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

lemma unitPlanarProfile_zero : unitPlanarProfile 0=0 := by
  simp [unitPlanarProfile,le_min (by norm_num : (0 : ℝ)≤2) (by positivity : 0≤2*Real.sqrt Real.pi)]

lemma unitPlanarProfile_one : unitPlanarProfile 1=0 := by
  simp [unitPlanarProfile,Real.sqrt_nonneg]

lemma open_outside_closure_of_not_frontier {X : Type*} [TopologicalSpace X]
    {O : Set X} (ho : IsOpen O) {x : X} (hx : x∉frontier O) (hn : x∉O) : x∉closure O := by
  intro hc
  exact hx ⟨hc,by simpa only [ho.interior_eq] using hn⟩

theorem isMinimizerAt_section_planar_profile_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
    ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  let A := centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)
  have hr : PlanarRadialDownset A := isMinimizerAt_centered_section_radial hV hmin hR hd i _
  have hv : volume.real A=volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)) :=
    centeredAxialSlice_volume _ b i _
  have hcorner (n : Fin 2 →Bool) : planarSquareCorner n∈A ↔
      quotientMap (axialSectionCorner b i t n)∈openRepresentative E := by
    change (torusAxialSplit i).symm ((t : AxisCircle),planarSquareCorner n+axialSectionCenter b i)∈openRepresentative E ↔ _
    rw [centered_section_corner]
  have hout (n : Fin 2 →Bool) (hn : quotientMap (axialSectionCorner b i t n)∉openRepresentative E) :
      quotientMap (axialSectionCorner b i t n)∉closure (openRepresentative E) :=
    open_outside_closure_of_not_frontier (isOpen_openRepresentative E) (hc n) hn
  by_cases hnear : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E
  · by_cases hfar : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∈openRepresentative E
    · have hAu : A=univ := by
        apply eq_univ_of_forall
        intro y
        apply hr _ _ (fun j ↦ ?_) ((hcorner _).mpr hfar)
        simp only [planarSquareCorner,ite_true]
        rw [axisCircle_norm_coe_small (by norm_num : |(1/2 : ℝ)|≤1/2)]
        simpa using axisCircle_norm_le_half (y j)
      have hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=1 := by
        rw [←hv,hAu]; simp
      rw [hs,unitPlanarProfile_one,ENNReal.ofReal_zero]
      exact bot_le
    · by_cases h0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · obtain ⟨L,hL,hband,hcal,hp⟩ := isMinimizerAt_section_complement_calibration hV hmin hR hd i t (hout _ hfar) h0 h1 hn
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _))).trans hp
        · have he0 : (fun k : Fin 2 ↦ if k=1 then false else true)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=1 then true else false)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_perimeter hV hmin hR hd i 1 ht (by rwa [he0]) (by rw [he1]; exact hout _ h1)
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))).trans (by simpa using hp)
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · have he0 : (fun k : Fin 2 ↦ if k=0 then false else true)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=0 then true else false)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_perimeter hV hmin hR hd i 0 ht (by rwa [he0]) (by rw [he1]; exact hout _ h0)
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))).trans (by simpa using hp)
        · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
            (isMinimizerAt_section_disk_perimeter hV hmin hR hd i t hnear (hout _ h0) (hout _ h1))
  · have hAe : A=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      apply hnear
      apply (hcorner _).mp
      apply hr _ _ _ hy
      intro j
      simp only [planarSquareCorner,Bool.false_eq_true,ite_false,norm_zero]
      exact norm_nonneg _
    have hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=0 := by
      rw [←hv,hAe]; simp
    rw [hs,unitPlanarProfile_zero,ENNReal.ofReal_zero]
    exact bot_le

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_section_planar_profile_oai := @OAI.CubicTorus.isMinimizerAt_section_planar_profile_oai
