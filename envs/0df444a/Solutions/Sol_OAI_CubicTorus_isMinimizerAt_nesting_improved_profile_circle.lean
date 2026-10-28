-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:14:06.876241+00:00
-- url     : https://prove2.me/submissions/329bf053-6983-4fb4-9d41-82404e2db196

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_bottom_both_extents
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_boundary_slice_null_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_corner_boundary_heights_null
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_section_improved_profile

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

lemma axialSlice_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : AxisCircle) :
    MeasurableSet (axialSlice E i t) :=
  hE.preimage ((torusAxialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id))

lemma axialSliceVolume_measurable {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    Measurable (axialSliceVolume E i) := by
  exact measurable_measure_prodMk_left (hE.preimage (torusAxialSplit i).symm.measurable)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma octantHeight_mem (b : Fin 3 → Bool) (i : Fin 3) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    octantHeight b i t∈Icc (1/2 : ℝ) 1 := by
  unfold octantHeight
  cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor <;> linarith [ht.1,ht.2]

lemma upperFold_slice_same (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (y : TransverseProduct) : upperFold ((torusAxialSplit i).symm ((t : AxisCircle),y)) i=t := by
  change 1-‖((torusAxialSplit i).symm ((t : AxisCircle),y)) i‖=t
  rw [torusAxialSplit_symm_same,circle_norm_upper ht]
  ring

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
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ActualAxialFlux
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

theorem isMinimizerAt_axialSlice_antitone {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) : AntitoneOn
      (fun t : ℝ ↦ axialSlice (openRepresentative E) i (octantHeight b i t : AxisCircle)) (Icc 0 1) := by
  intro s hs t ht hst y hyt
  let x := upperFold ((torusAxialSplit i).symm ((octantHeight b i s : AxisCircle),y))
  let z := upperFold ((torusAxialSplit i).symm ((octantHeight b i t : AxisCircle),y))
  have hxs : x∈closedUpperOctant := upperFold_mem _
  have hzt : z∈closedUpperOctant := upperFold_mem _
  have hxz : OrientedCoordinateLE b x z := by
    unfold OrientedCoordinateLE
    refine (Fin.forall_iff_succAbove i (P := fun j ↦ if b j then x j≤z j else z j≤x j)).mpr ?_
    constructor
    · have hxi := upperFold_slice_same i (octantHeight_mem b i hs) y
      have hzi := upperFold_slice_same i (octantHeight_mem b i ht) y
      change (if b i then x i≤z i else z i≤x i)
      change x i=octantHeight b i s at hxi
      change z i=octantHeight b i t at hzi
      rw [hxi,hzi]
      unfold octantHeight
      cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith
    · intro k
      have he : x (i.succAbove k)=z (i.succAbove k) :=
        (upperFold_slice_succAbove i _ y k).trans (upperFold_slice_succAbove i _ y k).symm
      change (if b (i.succAbove k) then x (i.succAbove k)≤z (i.succAbove k) else z (i.succAbove k)≤x (i.succAbove k))
      rw [he]
      split_ifs <;> exact le_rfl
  have hr := reflection_invariant_openRepresentative hmin.1.1 hR
  have hzo : quotientMap z∈openRepresentative E := (upperFold_phase hr _).mpr hyt
  have hxo := isMinimizerAt_closed_octant_order hV hmin hR hd hxs hzt hxz hzo
  exact (upperFold_phase hr _).mp hxo

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

lemma centeredAxialSlice_closure_subset (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) :
    closure (centeredAxialSlice O b i t)⊆centeredAxialSlice (closure O) b i t := by
  apply closure_minimal
  · exact preimage_mono (preimage_mono subset_closure)
  · exact (isClosed_closure.preimage ((torusAxialSplit_symm_continuous i).comp
      (continuous_const.prodMk (continuous_add_const (axialSectionCenter b i)))))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma openRepresentative_compl_eq {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    openRepresentative Eᶜ=(closure (openRepresentative E))ᶜ := by
  rw [isMinimizerAt_closure_openRepresentative_null hV hmin]
  simp only [openRepresentative,compl_compl]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

lemma extent_lower_bound {h s L : ℝ} (hL : 0 < L)
    (hcal : (1 - s) / L + Real.pi * L / 4 ≤ h * s) :
    2 / Real.pi * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) ≤ L := by
  have hp := Real.pi_pos
  have hh := (mul_le_mul_of_nonneg_right hcal (le_of_lt hL))
  have hsq : (h * s - Real.pi * L / 2) ^ 2 ≤ h ^ 2 * s ^ 2 - Real.pi * (1 - s) := by
    have heq : ((1 - s) / L + Real.pi * L / 4) * L = 1 - s + Real.pi * L ^ 2 / 4 := by
      field_simp
    rw [heq] at hh
    have hm := mul_le_mul_of_nonneg_left hh (le_of_lt hp)
    nlinarith
  have hs := Real.le_sqrt_of_sq_le hsq
  convert (show 2 * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) / Real.pi ≤ L from
    (div_le_iff₀ hp).2 (by nlinarith)) using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma endpoint_slack_bound {h s t₀ : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t₀) (hst : t₀ ≤ s)
    (hroot : h ^ 2 * t₀ ^ 2 = Real.pi * (1 - t₀)) :
    1 - 2 / Real.pi * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) ≤
      1 - 2 * h * t₀ / Real.pi +
        (2 / Real.pi * Real.sqrt (Real.pi + 2 * h ^ 2 * t₀)) * Real.sqrt (s - t₀) := by
  let Y := Real.sqrt (s - t₀)
  let R := Real.sqrt (Real.pi + 2 * h ^ 2 * t₀)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = s - t₀ := Real.sq_sqrt (sub_nonneg.2 hst)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = Real.pi + 2 * h ^ 2 * t₀ := Real.sq_sqrt (by positivity)
  have hupper : Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s)) ≤ R * Y + h * Y ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    have hm : 0 ≤ 2 * (R * Y) * (h * Y ^ 2) := by positivity
    have heq : h ^ 2 * s ^ 2 - Real.pi * (1 - s) = R ^ 2 * Y ^ 2 + h ^ 2 * Y ^ 4 := by
      rw [hR2]
      have hs : s = t₀ + Y ^ 2 := by linarith
      rw [hs]
      nlinarith [hroot]
    rw [heq]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hupper (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
  dsimp [R, Y] at hm hY2
  rw [hY2] at hm
  ring_nf at hm ⊢
  linarith only [hm]

theorem interval_placement {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (1033 / 2700 : ℝ) ≤ u h - dm ∧ (38 / 100 : ℝ) < u h - dm ∧
    1 / Real.pi < (38 / 100 : ℝ) ∧ u h ≤ 1 - 1 / Real.pi ∧
    u h < t h ∧ h * u h ≤ 24 / 25 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hh0 : 0 < h := by linarith [hh.1]
  have hu1 : u h ≤ 1 - 1 / Real.pi := min_le_left _ _
  have huv : u h ≤ (24 / 25 : ℝ) / h := min_le_right _ _
  have hu : (16 / 27 : ℝ) ≤ u h := by
    apply le_min
    · apply (le_sub_iff_add_le).2
      have hip : 1 / Real.pi ≤ (1 / 3 : ℝ) := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hp3))
      linarith
    · apply (le_div_iff₀ hh0).2
      linarith [hh.2]
  have hhU : h * u h ≤ 24 / 25 := by
    have := (le_div_iff₀ hh0).1 huv
    nlinarith
  have htr := t_spec hh0
  have hlt : u h < t h := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt htr.1) hn 2) (sq_nonneg h)
    have hsq := pow_le_pow_left₀ (mul_nonneg (le_of_lt hh0) (by linarith : 0 ≤ u h)) hhU 2
    have hip : 1 ≤ Real.pi * (1 - u h) := by
      have hh := mul_le_mul_of_nonneg_left hu1 (le_of_lt hp)
      field_simp at hh
      nlinarith
    nlinarith [htr.2.2]
  refine ⟨?_, ?_, ?_, hu1, hlt, hhU⟩
  · dsimp [dm]; linarith
  · dsimp [dm]; linarith
  · apply (div_lt_iff₀ hp).2
    nlinarith

lemma continuous_shape : Continuous shape := by
  unfold shape
  fun_prop

end CubicTorus.Shape
end
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

lemma axialSectionCenter_complement (b : Fin 3 →Bool) (i : Fin 3) (y : TransverseProduct) :
    (fun j ↦ y j+((1/2 : ℝ) : AxisCircle))+axialSectionCenter (fun k ↦ !b k) i=
      y+axialSectionCenter b i := by
  ext j
  simp only [Pi.add_apply,axialSectionCenter]
  by_cases hb : b (i.succAbove j)=true
  · simp [hb]
  · have hf : b (i.succAbove j)=false := Bool.eq_false_iff.mpr hb
    simp only [hf,Bool.not_false,ite_true,Bool.false_eq_true,ite_false,add_zero]
    rw [add_assoc,←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]

theorem isMinimizerAt_nested_edge_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {L : ℝ}
    (hfill : ∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →2*‖y j‖<L →
      y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle))
    {z : ℝ} (hz : z∈Icc (0 : ℝ) 1) {y : TransverseProduct}
    (hy : y∈closure (centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)))
    (hedge : ∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) :
    2*‖y j‖≤1-L := by
  have hsub : centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)⊆
      centeredAxialSlice (openRepresentative E) b i (octantHeight b i 0 : AxisCircle) :=
    preimage_mono (isMinimizerAt_axialSlice_antitone hV hmin hR hd i ⟨by norm_num,by norm_num⟩ hz hz.1)
  have hy0 := centeredAxialSlice_closure_subset (openRepresentative E) b i (octantHeight b i 0 : AxisCircle)
    (closure_mono hsub hy)
  by_contra hn
  have hh : 2*‖y j+((1/2 : ℝ) : AxisCircle)‖<L := by
    rw [axisCircle_norm_add_half]
    linarith
  have hyc := hfill (fun k ↦ y k+((1/2 : ℝ) : AxisCircle)) (fun k hk ↦ by
    rw [hedge k hk,←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]) hh
  rw [openRepresentative_compl_eq hV hmin] at hyc
  change (torusAxialSplit i).symm ((octantHeight b i 0 : AxisCircle),
    (fun k ↦ y k+((1/2 : ℝ) : AxisCircle))+axialSectionCenter (fun k ↦ !b k) i)∉closure (openRepresentative E) at hyc
  rw [axialSectionCenter_complement] at hyc
  exact hyc hy0

theorem isMinimizerAt_bottom_nested_endpoint {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    ∀ j : Fin 2,∀ z∈Icc (0 : ℝ) 1,∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)),
      (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →
      2*‖y j‖≤1-2/Real.pi*((H/2)*s-Real.sqrt ((H/2)^2*s^2-Real.pi*(1-s))) := by
  intro s j z hz y hy hedge
  obtain ⟨_,_,hb⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  obtain ⟨L,hL,hband,hfill,hcal⟩ := hb j
  have he := isMinimizerAt_nested_edge_bound hV hmin hR hd i j hfill hz hy hedge
  have hlow := Shape.extent_lower_bound hL.1 hcal
  dsimp only [s]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma nestingDelta_mem (h s : ℝ) : nestingDelta h s∈Icc 0 Shape.dm := by
  exact ⟨le_min (by norm_num [Shape.dm]) (le_max_right _ _),min_le_left _ _⟩

lemma nestingDelta_gap {h s : ℝ} (hh : h∈Icc (51/50 : ℝ) (81/50 : ℝ))
    (hd : 0<nestingDelta h s) : max 0 (nestingEndpointBound h s)≤Shape.u h-nestingDelta h s := by
  have hpos : 0<Shape.u h-nestingEndpointBound h s := by
    have hm : 0 < max (Shape.u h-nestingEndpointBound h s) 0 :=
      hd.trans_le (min_le_right _ _)
    exact (lt_max_iff.mp hm).resolve_right (lt_irrefl _)
  have hsub : nestingDelta h s≤Shape.u h-nestingEndpointBound h s := by
    dsimp only [nestingDelta]
    rw [max_eq_left hpos.le]
    exact min_le_right _ _
  have hplace := (Shape.interval_placement hh).2.1
  have hcap := (nestingDelta_mem h s).2
  apply max_le <;> linarith

lemma source_root_le_of_bottom {h s : ℝ} (hh : 0<h) (hs : 0 ≤ s)
    (hdisc : Real.pi*(1-s)≤(h*s)^2) : Shape.t h ≤ s := by
  have ht := Shape.t_spec hh
  by_contra hn
  have hst : s<Shape.t h := lt_of_not_ge hn
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 2) (sq_nonneg h)
  have hp := mul_lt_mul_of_pos_left hst Real.pi_pos
  nlinarith [ht.2.2]

lemma nestingEndpointBound_ge_exact {h s : ℝ} (hh : 0<h) (hs : 0 ≤ s)
    (hdisc : Real.pi*(1-s)≤(h*s)^2) :
    1-2/Real.pi*(h*s-Real.sqrt (h^2*s^2-Real.pi*(1-s)))≤nestingEndpointBound h s := by
  have ht := Shape.t_spec hh
  have hts := source_root_le_of_bottom hh hs hdisc
  have hb := Shape.endpoint_slack_bound hh.le ht.1.le hts ht.2.2
  simpa only [nestingEndpointBound] using hb

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

lemma octantHeight_surjective_half (b : Fin 3 →Bool) (i : Fin 3) {t : ℝ}
    (ht : t∈Icc (1/2 : ℝ) 1) : ∃ z∈Icc (0 : ℝ) 1,octantHeight b i z=t := by
  cases hb : b i
  · refine ⟨2-2*t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
    simp only [octantHeight,hb,Bool.false_eq_true,ite_false]
    ring
  · refine ⟨2*t-1,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simp only [octantHeight,hb,ite_true]
    ring

theorem isMinimizerAt_nesting_improved_profile_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    0<δ →∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),
      let v := volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))
      v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  intro s δ hδpos
  have hδ : δ∈Icc 0 Shape.dm := nestingDelta_mem _ _
  have hh : 0<H/2 := by linarith [hH.1]
  obtain ⟨_,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  have hbound := nestingEndpointBound_ge_exact hh (show 0 ≤ s from measureReal_nonneg) hdisc
  let e := max 0 (nestingEndpointBound (H/2) s)
  have he : 0≤e := le_max_left _ _
  have hegap : e≤Shape.u (H/2)-δ := nestingDelta_gap hH hδpos
  have hplace := Shape.interval_placement hH
  have hc : ∀ᵐ t : ℝ,∀ n : Fin 2 →Bool,
      quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E) := by
    rw [ae_all_iff]
    intro n
    exact ae_iff.mpr (by simpa only [not_not] using isMinimizerAt_corner_boundary_heights_null hV hE hmin hR b i n)
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hn := hp.quasiMeasurePreserving.ae (isMinimizerAt_boundary_slice_null_ae hV hE hmin i)
  have hsub : Icc (1/2 : ℝ) 1⊆Ioc 0 1 := fun t ht ↦ ⟨by linarith [ht.1],ht.2⟩
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae_restrict_of_subset hsub hn,
    ae_restrict_mem measurableSet_Icc] with t htc htn ht
  intro v hvrange
  let q := (v-Shape.u (H/2)+δ)/δ
  have hq : q∈Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hvrange.1]) hδpos.le,
    (div_le_one hδpos).mpr (by linarith [hvrange.2])⟩
  have hvrepr : v=Shape.u (H/2)-δ+δ*q := by dsimp only [q]; field_simp; ring
  have hvlo : (38/100 : ℝ)<v := by linarith [hplace.2.1,hδ.2,hvrange.1]
  apply isMinimizerAt_section_improved_profile hV hmin hR hd i ht htc htn he hδ hq hplace.2.2.2.1 hegap hvrepr hvlo
  intro j y hy hyedge
  obtain ⟨z,hz,hzt⟩ := octantHeight_surjective_half b i ht
  have hb := isMinimizerAt_bottom_nested_endpoint hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 j z hz y (by rwa [hzt]) hyedge
  exact (hb.trans hbound).trans (le_max_right _ _)

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nesting_improved_profile_circle_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    0<δ →∀ᵐ t : AxisCircle,
      let v := volume.real (axialSlice (openRepresentative E) i t)
      v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  intro s δ hδpos
  apply circle_ae_of_upper_half
  · let v : AxisCircle →ℝ := fun t ↦ volume.real (axialSlice (openRepresentative E) i t)
    have hm : Measurable v := (axialSliceVolume_measurable (isOpen_openRepresentative E).measurableSet i).ennreal_toReal
    have hf : Measurable (fun t : AxisCircle ↦ ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v t-Shape.u (H/2)+δ)/δ)))) := by
      apply Measurable.ennreal_ofReal
      apply measurable_const.mul
      apply Real.continuous_sqrt.measurable.comp
      exact measurable_const.add (measurable_const.mul (Shape.continuous_shape.measurable.comp ((hm.sub_const _).add_const _ |>.div_const _)))
    have hi := measurableSet_le hf (planarTorusPerimeter_slice_measurable (isOpen_openRepresentative E).measurableSet i)
    have hr : MeasurableSet {t : AxisCircle | v t∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2))} := hm measurableSet_Icc
    convert hr.compl.union hi using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff]
    tauto
  · intro t
    rw [axialSlice_neg_of_reflection (reflection_invariant_openRepresentative hmin.1.1 hR)]
  · exact isMinimizerAt_nesting_improved_profile_ae hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH hδpos

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle_oai := @OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle_oai
