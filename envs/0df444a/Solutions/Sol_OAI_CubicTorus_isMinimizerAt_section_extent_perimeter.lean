-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_section_extent_perimeter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:26:31.874188+00:00
-- url     : https://prove2.me/submissions/fdfd99a4-c368-44dd-8c8c-9cf691fc8eab

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma primitive_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ u in (0 : ℝ)..t, b u) := by
  have hd (t : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.continuous.intervalIntegrable 0 t) (hb.continuous.stronglyMeasurableAtFilter volume _)
    hb.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (hd t).differentiableAt,?_⟩
  simpa only [funext (fun t ↦ (hd t).deriv)] using hb

lemma intervalSmoothHat_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (a c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (intervalSmoothHat b a c) :=
  ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const)).sub
    ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const))

lemma intervalSmoothHat_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : HasDerivAt (intervalSmoothHat b a c) (b (t-a)-b (t-c)) t := by
  have hd (x : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable 0 x) (hb.stronglyMeasurableAtFilter volume _) hb.continuousAt
  change HasDerivAt (fun x : ℝ ↦ (∫ u in (0 : ℝ)..x-a, b u) -
    ∫ u in (0 : ℝ)..x-c, b u) _ _
  simpa only [Function.comp_def,mul_one,id_eq,Pi.sub_def] using
    ((hd (t-a)).comp t ((hasDerivAt_id t).sub_const a)).sub
      ((hd (t-c)).comp t ((hasDerivAt_id t).sub_const c))

lemma intervalSmoothHat_eq_integral {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : intervalSmoothHat b a c t = ∫ u in t-c..t-a, b u := by
  rw [intervalSmoothHat]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hb.intervalIntegrable 0 (t-c)) (hb.intervalIntegrable (t-c) (t-a))
  linarith

lemma intervalSmoothHat_nonneg {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ t, 0 ≤ b t) {a c : ℝ} (hac : a ≤ c) (t : ℝ) :
    0 ≤ intervalSmoothHat b a c t := by
  rw [intervalSmoothHat_eq_integral hb]
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ hb0 _)

lemma intervalSmoothHat_le_one {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {a c : ℝ} (hac : a ≤ c) (t : ℝ) : intervalSmoothHat b a c t ≤ 1 := by
  rw [intervalSmoothHat_eq_integral hb,intervalIntegral.integral_of_le (by linarith)]
  rw [← hb1]
  exact setIntegral_le_integral hbi (ae_of_all _ hb0)

lemma intervalSmoothHat_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c) :
    tsupport (intervalSmoothHat b a c) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  rw [intervalSmoothHat_eq_integral hb]
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro u hu
  have htc : t-c ≤ t-a := by linarith
  rw [uIoc_of_le htc] at hu
  apply image_eq_zero_of_notMem_tsupport
  intro hub
  have hur := hs hub
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hl|hr
  · linarith [hu.2,hur.1]
  · linarith [hu.1,hur.2]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finite_integer_support_near {f : ℝ → ℝ} (hf : HasCompactSupport f) (a : ℝ) :
    ∃ s : Finset ℤ,∀ x∈Metric.ball a 1,∀ n∉s,f (x+n)=0 := by
  classical
  obtain ⟨R,_,hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|a|+1)
  refine ⟨Finset.Icc (-(N : ℤ)) N,?_⟩
  intro x hx n hn
  by_contra h
  have hb := hR _ (subset_tsupport f h)
  have hx' : |x-a|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
  have ha : |x|≤|a|+1 := by
    have hh := abs_add_le (x-a) a
    rw [sub_add_cancel] at hh
    linarith
  have hn' : |(n : ℝ)|<N := by
    have hh := norm_sub_le (x+n) x
    simp only [Real.norm_eq_abs] at hh
    rw [add_sub_cancel_left] at hh
    rw [Real.norm_eq_abs] at hb
    linarith
  apply hn
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hn'.le).1
  · exact_mod_cast (abs_le.mp hn'.le).2

lemma circlePeriodize_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) : ContDiff ℝ (⊤ : ℕ∞) (circlePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨s,hs⟩ := finite_integer_support_near hs a
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∑ n∈s,f (x+n)) :=
    ContDiff.sum fun n _ ↦ hf.comp (contDiff_id.add contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0 : ℝ)<1)] with x hx
  exact tsum_eq_sum (hs x hx)

lemma circlePeriodize_eventuallyEq {f : ℝ → ℝ} (hc : HasCompactSupport f)
    {a : ℝ} (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    {x : ℝ} (hx : x∈Icc (a-1/2) (a+1/2)) : circlePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s,hlocal⟩ := finite_integer_support_near hc x
  have hz (n : ℤ) (hn : n≠0) : ∀ᶠ y in 𝓝 x,f (y+n)=0 := by
    have hnot : x+n∉tsupport f := by
      intro h
      have hh := hs h
      have hlo : (-1 : ℝ)<n := by linarith [hx.2,hh.1]
      have hhi : (n : ℝ)<1 := by linarith [hx.1,hh.2]
      have hlo' : (-1 : ℤ)<n := by exact_mod_cast hlo
      have hhi' : n<1 := by exact_mod_cast hhi
      omega
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x,∀ n∈s,n≠0 → f (y+n)=0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n=0
    · exact Eventually.of_forall fun _ h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun _ h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1),hfin] with y hy hz
  unfold circlePeriodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    by_cases hs : n∈s
    · exact hz n hs hn
    · exact hlocal y hy n hs

lemma circlePeriodize_unit_bounds {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,0≤f x ∧ f x≤1) (x : ℝ) :
    0 ≤ circlePeriodize f x ∧ circlePeriodize f x≤1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    unfold circlePeriodize
    simp only [hn,tsum_zero,le_refl,zero_le_one,and_self]

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

lemma circlePeriodize_integral_short {f : ℝ → ℝ}
    (hc : HasCompactSupport f) {d : ℝ}
    (hs : tsupport f ⊆ Ioo (d-1/2) (d+1/2)) :
    (∫ t : AxisCircle,(circlePeriodize_periodic f).lift t)=∫ t : ℝ,f t := by
  rw [←AddCircle.intervalIntegral_preimage (1 : ℝ) (d-1/2),show d-1/2+1=d+1/2 by ring]
  calc
    _=∫ t in (d-1/2)..d+1/2,f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (circlePeriodize_eventuallyEq hc hs (by
        simpa only [uIcc_of_le (show d-1/2≤d+1/2 by linarith)] using ht)).eq_of_nhds
    _=∫ t : ℝ,f t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      exact image_eq_zero_of_notMem_tsupport (fun hh ↦ ht ⟨(hs hh).1,(hs hh).2.le⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    (j : Fin 2) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y j=(a : AxisCircle) → y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε → ∀ y : TransverseProduct,y j=(t : AxisCircle) → y∈A := by
  have hc : IsCompact Aᶜ := hA.isClosed_compl.isCompact
  have hj : Continuous (Function.eval j : TransverseProduct → AxisCircle) := continuous_apply j
  have ho : IsOpen ((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := (hc.image hj).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval j '' Aᶜ)ᶜ : Set AxisCircle) := by
    rintro ⟨y,hy,he⟩
    exact hy (ha y he)
  have hpre := ho.preimage (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre a hm
  refine ⟨ε,hε,fun t ht y hy ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,hny,hy⟩

end CubicTorus

end
end

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarProductField_admissible {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    PlanarAdmissibleField (planarProductField σ a b) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞))
  refine ⟨((hσ.comp hx).mul (ha.comp hy)).smul contDiff_const |>.add
    ((hb.comp hy).smul contDiff_const),?_,?_⟩
  · intro n y
    unfold planarProductField
    simp only [PiLp.add_apply]
    have hs := pσ.int_mul (n 0) (y 0)
    have ha := pa.int_mul (n 1) (y 1)
    have hb := pb.int_mul (n 1) (y 1)
    simp only [mul_one] at hs ha hb
    rw [hs,ha,hb]
  · intro y
    have hs : (σ (y 0))^2≤1 := by nlinarith [sq_abs (σ (y 0)),hσb (y 0),abs_nonneg (σ (y 0))]
    have hn : ‖planarProductField σ a b y‖^2≤1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two,planarProductField,PiLp.add_apply,PiLp.smul_apply,
        PiLp.single_apply,Fin.isValue,ite_true,smul_eq_mul,
        mul_one,Fin.reduceEq,ite_false,mul_zero,add_zero,zero_add,Real.norm_eq_abs,sq_abs]
      nlinarith [hab (y 1),mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (a (y 1)))]
    nlinarith [norm_nonneg (planarProductField σ a b y)]

lemma planeDivergence_planarProductField {σ a b : ℝ → ℝ}
    (hσ : Differentiable ℝ σ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (y : Plane) : planeDivergence (planarProductField σ a b) y=
      deriv σ (y 0)*a (y 1)+deriv b (y 1) := by
  have hx := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hy := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := y)
  have hd := (((hσ (y 0)).hasDerivAt.comp_hasFDerivAt y hx).mul
    ((ha (y 1)).hasDerivAt.comp_hasFDerivAt y hy)).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have he := ((hb (y 1)).hasDerivAt.comp_hasFDerivAt y hy).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  have hf := hd.add he
  change HasFDerivAt (planarProductField σ a b) _ y at hf
  rw [planeDivergence,hf.fderiv]
  simp [ContinuousLinearMap.smulRight_apply,mul_comm]

theorem planarTorusPerimeter_ge_product_flux (A : Set TransverseProduct)
    {σ a b : ℝ → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (pσ : Function.Periodic σ 1) (pa : Function.Periodic a 1) (pb : Function.Periodic b 1)
    (hσb : ∀ x,|σ x|≤1) (hab : ∀ y,(a y)^2+(b y)^2≤1) :
    ENNReal.ofReal (∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
      (real_periodic_deriv pb).lift (y 1))≤planarTorusPerimeter A := by
  have he (y : TransverseProduct) :
      planeDivergence (planarProductField σ a b) (planarRepresentative y)=
        (real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
          (real_periodic_deriv pb).lift (y 1) := by
    rw [planeDivergence_planarProductField (hσ.differentiable (by simp))
      (ha.differentiable (by simp)) (hb.differentiable (by simp))]
    have e0 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 0)
    have e1 := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (y 1)
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 0) : ℝ) : AxisCircle)=y 0 at e0
    change (((AddCircle.equivIco (1 : ℝ) 0) (y 1) : ℝ) : AxisCircle)=y 1 at e1
    conv_rhs => rw [←e0,←e1]
    rfl
  rw [←show (∫ y in A,planeDivergence (planarProductField σ a b) (planarRepresentative y))=
      ∫ y in A,(real_periodic_deriv pσ).lift (y 0)*pa.lift (y 1)+
        (real_periodic_deriv pb).lift (y 1) by apply integral_congr_ae; exact Filter.Eventually.of_forall he]
  exact le_iSup_of_le (planarProductField σ a b)
    (le_iSup_of_le (planarProductField_admissible hσ ha hb pσ pa pb hσb hab) le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma transverse_integral_mul (f g : AxisCircle → ℝ) :
    (∫ y : TransverseProduct,f (y 0)*g (y 1))=(∫ t,f t)*(∫ t,g t) := by
  simpa only [Fin.prod_univ_two,Fin.isValue,Fin.reduceFinMk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons] using
    integral_fintype_prod_volume_eq_prod (E := fun _ : Fin 2 ↦ AxisCircle) ![f,g]

theorem planarTorusPerimeter_ge_weighted_bump_strips
    {A : Set TransverseProduct} (hA : MeasurableSet A)
    {T : Set AxisCircle} (hT : MeasurableSet T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c)
    (hshort : c-a+2*r<1)
    (hin : ∀ t : ℝ,b (t-a)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y 1∈T → y∈A)
    (hout : ∀ t : ℝ,b (t-c)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y∉A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
      (intervalSmoothHat_support hb.continuous hs hac)
  let B : ℝ → ℝ := fun t ↦ b (t-a)
  have hBs : tsupport B ⊆ Ioo (d-1/2) (d+1/2) := by
    intro t ht
    have hh := hs (tsupport_comp_subset_preimage b (continuous_id.sub continuous_const) ht)
    change -r≤t-a ∧ t-a ≤ r at hh
    dsimp only [d]
    constructor <;> linarith [hh.1,hh.2]
  have hBc : HasCompactSupport B :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
      (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hb.comp (contDiff_id.sub contDiff_const)
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*(b (t-a)-b (t-c)) := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc).differentiable (by simp) t),
      he.deriv_eq,(intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv]
  let β : AxisCircle → ℝ := (circlePeriodize_periodic B).lift
  have hβ : Continuous β := continuous_periodic_lift _ (circlePeriodize_contDiff hB hBc).continuous
  have hβi : (∫ t,β t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self b a).trans hb1
  have huC : Continuous (pu.lift : AxisCircle → ℝ) := continuous_periodic_lift _ hu.continuous
  have hvC : Continuous ((real_periodic_deriv pv).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hv.continuous_deriv (by simp))
  have hσC : Continuous ((real_periodic_deriv hp).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hψ.continuous_deriv (by simp))
  have huL (t : AxisCircle) : 0≤pu.lift t := by
    induction t using Quotient.inductionOn with | h t => exact hu0 t
  have he (y : TransverseProduct) :
      2*β (y 0)*(T.indicator pu.lift (y 1))≤
        A.indicator (fun y : TransverseProduct ↦ (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) y := by
    let t : ℝ := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0) : ℝ)
    have ht0 := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0)).property
    have ht : t∈Icc (d-1/2) (d+1/2) := by
      change d-1/2≤t ∧ t<d-1/2+1 at ht0
      constructor <;> linarith [ht0.1,ht0.2]
    have hty : (t : AxisCircle)=y 0 := (AddCircle.equivIco (1 : ℝ) (d-1/2)).symm_apply_apply _
    have hBt : β (y 0)=b (t-a) := by
      rw [←hty]
      exact (circlePeriodize_eventuallyEq hBc hBs ht).eq_of_nhds
    rw [hBt]
    by_cases hy : y∈A
    · have hc0 : b (t-c)=0 := by
        by_contra hnc
        exact hout t hnc y hty.symm hy
      rw [indicator_of_mem hy]
      have hd' : (real_periodic_deriv hp).lift (y 0)=2*b (t-a) := by
        rw [←hty]
        change deriv ψ t=2*b (t-a)
        rw [hd t ht,hc0,sub_zero]
      rw [hd']
      by_cases hyT : y 1∈T
      · rw [indicator_of_mem hyT]
      · rw [indicator_of_notMem hyT,mul_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (hb0 _)) (huL _)
    · rw [indicator_of_notMem hy]
      by_cases hyT : y 1∈T
      · have ha0 : b (t-a)=0 := by
          by_contra hna
          exact hy (hin t hna y hty.symm hyT)
        rw [ha0,mul_zero,zero_mul]
      · rw [indicator_of_notMem hyT,mul_zero]
  have hiR : Integrable (fun y : TransverseProduct ↦
      (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) :=
    ((hσC.comp (continuous_apply 0)).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*T.indicator pu.lift (y 1)) := by
    have hbase : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*pu.lift (y 1)) :=
      ((continuous_const.mul (hβ.comp (continuous_apply 0))).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply (hbase.indicator (hT.preimage (measurable_pi_apply 1))).congr
    filter_upwards [] with y
    by_cases hy : y 1∈T <;> simp [hy]
  have hle := integral_mono hiL (hiR.indicator hA) he
  have hlow : (∫ y : TransverseProduct,2*β (y 0)*T.indicator pu.lift (y 1))=
      2*(∫ t in T,pu.lift t) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,transverse_integral_mul,hβi,one_mul,integral_indicator hT]
  rw [hlow,integral_indicator hA] at hle
  have hvI : Integrable (fun y : TransverseProduct ↦ (real_periodic_deriv pv).lift (y 1)) :=
    (hvC.comp (continuous_apply 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hflux := planarTorusPerimeter_ge_product_flux A hψ hu hv hp pu pv hbψ huv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hflux
  rw [integral_add hiR.integrableOn hvI.integrableOn]
  have hev : (∫ y in A,(real_periodic_deriv pv).lift (y 1))=k*volume.real A := by
    calc
      _=∫ _ in A,k := setIntegral_congr_fun hA hk
      _=k*volume.real A := by simp [mul_comm,measureReal_def]
  rw [hev]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_open_partial_fiber_collar {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T) (a : ℝ)
    (ha : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : ℝ,|t-a|<ε →∀ y : TransverseProduct,y 0=(t : AxisCircle) →y 1∈T →y∈A := by
  have h1 : Continuous (Function.eval (1 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 1
  have h0 : Continuous (Function.eval (0 : Fin 2) : TransverseProduct → AxisCircle) := continuous_apply 0
  have hc : IsCompact (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T) :=
    (hA.isClosed_compl.inter (hT.isClosed.preimage h1)).isCompact
  have ho : IsOpen ((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) :=
    (hc.image h0).isClosed.isOpen_compl
  have hm : (a : AxisCircle)∈((Function.eval (0 : Fin 2) '' (Aᶜ∩(Function.eval (1 : Fin 2)) ⁻¹' T))ᶜ : Set AxisCircle) := by
    rintro ⟨y,⟨hy,hyT⟩,he⟩
    exact hy (ha y he hyT)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (ho.preimage (AddCircle.continuous_mk' (1 : ℝ))) a hm
  refine ⟨ε,hε,fun t ht y hy hyT ↦ ?_⟩
  have hh := hball (show t∈Metric.ball a ε from by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  by_contra hny
  exact hh ⟨y,⟨hny,hyT⟩,hy⟩

theorem planarTorusPerimeter_ge_corner_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {a c : ℝ} (hac : a ≤ c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=(c : AxisCircle) →y∉closure A)
    {k : ℝ} (hk : ∀ y∈A,(real_periodic_deriv pv).lift (y 1)=k) :
    ENNReal.ofReal (k*volume.real A+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  obtain ⟨ε,hε,hεA⟩ := planar_open_partial_fiber_collar hA hT a hin
  obtain ⟨δ,hδ,hδA⟩ := planar_open_fiber_collar isClosed_closure.isOpen_compl 0 c hout
  let r : ℝ := min (min ε δ) (1-(c-a))/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r<ε := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_left ε δ)
    dsimp only [r]; linarith
  have hrδ : r<δ := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_right ε δ)
    dsimp only [r]; linarith
  have hrc : c-a+2*r<1 := by
    have hh := min_le_right (min ε δ) (1-(c-a))
    dsimp only [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  apply planarTorusPerimeter_ge_weighted_bump_strips hA.measurableSet hT.measurableSet
    hu hv pu pv hu0 huv b.contDiff_normed b.integrable_normed (fun t ↦ b.nonneg_normed t)
    b.integral_normed (r := r) (a := a) (c := c) _ hac hrc _ _ hk
  · rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [sub_eq_add_neg,zero_add]
    exact Subset.rfl
  · intro t ht y hy hyT
    have hs : t-a∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-a| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hεA t (hab.trans hrε) y hy hyT
  · intro t ht y hy hya
    have hs : t-c∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-c| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hδA t (hab.trans hrδ) y hy (subset_closure hya)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_abs_lt_one {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,|f x|<1) (x : ℝ) : |circlePeriodize f x|<1 := by
  classical
  by_cases hn : ∃ n : ℤ,f (x+n)≠0
  · obtain ⟨n,hn⟩ := hn
    have huniq (m : ℤ) (hm : m≠n) : f (x+m)=0 := by
      by_contra hm'
      have h1 := hs (subset_tsupport f hn)
      have h2 := hs (subset_tsupport f hm')
      have hlo : (-1 : ℝ)<(m-n : ℤ) := by push_cast; linarith [h1.2,h2.1]
      have hhi : ((m-n : ℤ) : ℝ)<1 := by push_cast; linarith [h1.1,h2.2]
      have hlo' : (-1 : ℤ) < m-n := by exact_mod_cast hlo
      have hhi' : m-n<1 := by exact_mod_cast hhi
      omega
    rw [circlePeriodize,tsum_eq_single n huniq]
    exact hb _
  · push Not at hn
    simp only [circlePeriodize,hn,tsum_zero,abs_zero,zero_lt_one]

theorem exists_planar_affine_band_field {L q : ℝ} (hL : L∈Ioo 0 (1/2))
    (hq : q∈Ioo 0 1) :
    ∃ u v : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧ContDiff ℝ (⊤ : ℕ∞) v ∧
      Function.Periodic u 1 ∧Function.Periodic v 1 ∧
      (∀ y,0≤u y) ∧(∀ y,(u y)^2+(v y)^2=1) ∧
      (∀ y,|y|≤L →u y=Real.sqrt (1-(q/L*y)^2)) ∧
      (∀ y,|y|<L →deriv v y=q/L) := by
  have hLq : L<L/q := (lt_div_iff₀ hq.1).mpr (by nlinarith [hL.1,hq.2])
  obtain ⟨R,hLR,hR⟩ := exists_between (lt_min hL.2 hLq)
  have hRhalf : R<1/2 := hR.trans_le (min_le_left _ _)
  have hqR : (q/L)*R<1 := by
    have hh := (lt_div_iff₀ hq.1).mp (hR.trans_le (min_le_right _ _))
    rw [div_mul_eq_mul_div]
    apply (div_lt_one hL.1).mpr
    nlinarith
  let χ : ContDiffBump (0 : ℝ) := ⟨L,R,hL.1,hLR⟩
  let f : ℝ → ℝ := fun t ↦ (q/L*t)*χ t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_const.mul contDiff_id).mul χ.contDiff
  have hfs : tsupport f ⊆ Ioo ((0 : ℝ)-1/2) (0+1/2) := by
    apply (tsupport_mul_subset_right (f := fun t ↦ q/L*t) (g := χ)).trans
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f)
      (fun _ ht ↦ ⟨(hfs ht).1.le,(hfs ht).2.le⟩)
  have hfb (t : ℝ) : |f t|<1 := by
    by_cases hz : χ t=0
    · simp [f,hz]
    have ht : |t|<R := by
      have hh : t∈Metric.ball (0 : ℝ) R := by rwa [←χ.support_eq]
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
    have hqL : 0<q/L := div_pos hq.1 hL.1
    calc
      |f t|=(q/L)* |t| *χ t := by simp only [f,abs_mul,abs_of_pos hqL,abs_of_nonneg χ.nonneg]
      _≤(q/L)* |t| := mul_le_of_le_one_right (mul_nonneg hqL.le (abs_nonneg _)) χ.le_one
      _<(q/L)*R := mul_lt_mul_of_pos_left ht hqL
      _<1 := hqR
  let v := circlePeriodize f
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := circlePeriodize_contDiff hf hfc
  have hpv : Function.Periodic v 1 := circlePeriodize_periodic f
  have hvb (t : ℝ) : |v t|<1 := circlePeriodize_abs_lt_one hfs hfb t
  have hpos (t : ℝ) : 0<1-(v t)^2 := by
    nlinarith [hvb t,abs_nonneg (v t),sq_abs (v t)]
  let u : ℝ → ℝ := fun t ↦ Real.sqrt (1-(v t)^2)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := (contDiff_const.sub (hv.pow 2)).sqrt (fun t ↦ (hpos t).ne')
  have hpu : Function.Periodic u 1 := fun t ↦ by dsimp only [u]; rw [hpv t]
  refine ⟨u,v,hu,hv,hpu,hpv,fun t ↦ Real.sqrt_nonneg _,?_,?_,?_⟩
  · intro t
    dsimp only [u]
    rw [Real.sq_sqrt (hpos t).le]
    ring
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_le.mp ht
      constructor <;> linarith
    have hχ : χ t=1 := χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using ht)
    dsimp only [u,v]
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).eq_of_nhds]
    simp only [f,hχ,mul_one]
  · intro t ht
    have htc : t∈Icc ((0 : ℝ)-1/2) (0+1/2) := by
      obtain ⟨ht0,ht1⟩ := abs_lt.mp ht
      constructor <;> linarith
    have hχ := χ.eventuallyEq_one_of_mem_ball (show t∈Metric.ball (0 : ℝ) L from by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
    have he : f=ᶠ[𝓝 t](fun t : ℝ ↦ q/L*t) := by
      filter_upwards [hχ] with x hx
      simp only [f,hx,Pi.one_apply,mul_one]
    change deriv (circlePeriodize f) t=q/L
    rw [(circlePeriodize_eventuallyEq hfc hfs htc).deriv_eq,he.deriv_eq]
    simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma closedCentralArc_isCompact (K : ℝ) : IsCompact (closedCentralArc K) :=
  isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))

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

lemma integral_closedCentralArc {K : ℝ} (hK : K∈Ico 0 (1/2)) (f : AxisCircle →ℝ) :
    (∫ z in closedCentralArc K,f z)=∫ t in (-K)..K,f (t : AxisCircle) := by
  have hsub : Icc (-K) K ⊆ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2,hK.2]
  have he (t : ℝ) (ht : t∈Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1)) :
      (t : AxisCircle)∈closedCentralArc K ↔t∈Icc (-K) K := by
    constructor
    · rintro ⟨s,hs,hst⟩
      have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub hs) ht).mp hst
      rwa [←hh]
    · intro ht
      exact ⟨t,ht,rfl⟩
  calc
    _=∫ z : AxisCircle,(closedCentralArc K).indicator f z :=
      (integral_indicator (closedCentralArc_isCompact K).measurableSet).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(closedCentralArc K).indicator f (t : AxisCircle) :=
      (AddCircle.integral_preimage (1 : ℝ) (-(1/2 : ℝ)) _).symm
    _=∫ t in Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1),(Icc (-K) K).indicator
        (fun t : ℝ ↦ f (t : AxisCircle)) t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      by_cases htk : t∈Icc (-K) K
      · simp only [indicator_of_mem htk,indicator_of_mem ((he t ht).mpr htk)]
      · simp only [indicator_of_notMem htk,indicator_of_notMem (mt (he t ht).mp htk)]
    _=∫ t in Icc (-K) K,f (t : AxisCircle) := by
      rw [setIntegral_indicator measurableSet_Icc,inter_eq_right.mpr hsub]
    _=∫ t in (-K)..K,f (t : AxisCircle) := by
      rw [intervalIntegral.integral_of_le (by linarith [hK.1]),integral_Icc_eq_integral_Ioc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_scaled_semicircle {L : ℝ} (hL : 0<L) :
    (∫ t in (-L)..L,Real.sqrt (1-(t/L)^2))=Real.pi*L/2 := by
  have hi := intervalIntegral.integral_comp_div (fun t : ℝ ↦ Real.sqrt (1-t^2))
    (a := -L) (b := L) hL.ne'
  rw [neg_div,div_self hL.ne',integral_sqrt_one_sub_sq] at hi
  calc
    _=L*(Real.pi/2) := hi
    _=Real.pi*L/2 := by ring

theorem planarTorusPerimeter_ge_semicircle_calibration
    {A : Set TransverseProduct} (hA : IsOpen A) {L : ℝ} (hL : L∈Ioo 0 (1/2))
    (hband : ∀ y∈A,∃ t : ℝ,|t|<L ∧(t : AxisCircle)=y 1)
    (hin : ∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A) :
    ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  let f : ℝ →ℝ := fun t ↦ Real.sqrt (1-(t/L)^2)
  have hf : Continuous f := (continuous_const.sub ((continuous_id.div_const L).pow 2)).sqrt
  have hb (q : ℝ) (hq : q∈Ioo 0 1) :
      ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A := by
    obtain ⟨u,v,hu,hv,pu,pv,hu0,huv,huBand,hvBand⟩ := exists_planar_affine_band_field hL hq
    have hqL : 0<q*L := mul_pos hq.1 hL.1
    have hqLL : q*L<L := by nlinarith [hq.2,hL.1]
    have hKhalf : q*L<1/2 := hqLL.trans hL.2
    have hbound := planarTorusPerimeter_ge_corner_calibration hA (closedCentralArc_isCompact (q*L))
      hu hv pu pv hu0 (fun t ↦ (huv t).le) (a := 0) (c := 1/2) (by norm_num) (by norm_num)
      (fun y hy0 hyT ↦ ?_) hout (k := q/L) (fun y hy ↦ ?_)
    · have hInt : (∫ t in (-(q*L))..(q*L),f t)≤∫ z in closedCentralArc (q*L),pu.lift z := by
        rw [integral_closedCentralArc ⟨hqL.le,hKhalf⟩]
        change (∫ t in (-(q*L))..(q*L),f t)≤∫ t in (-(q*L))..(q*L),u t
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _) (hu.continuous.intervalIntegrable _ _)
        intro t ht
        have htL : |t|≤L := (abs_le.mpr ht).trans hqLL.le
        rw [huBand t htL]
        apply Real.sqrt_le_sqrt
        have hq2 : q^2≤1 := by nlinarith [hq.1,hq.2]
        have hmul := mul_nonneg (sq_nonneg (t/L)) (sub_nonneg.mpr hq2)
        have he : (q/L*t)^2=q^2*(t/L)^2 := by ring
        rw [he]
        nlinarith
      exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hbound
    · obtain ⟨t,ht,he⟩ := hyT
      have htt : |t|<L := (abs_le.mpr ht).trans_lt hqLL
      exact hin t htt y (by simpa using hy0) he.symm
    · obtain ⟨t,ht,he⟩ := hband y hy
      rw [←he]
      exact hvBand t ht
  have hp : Continuous (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z,f t) :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable _ _) 0
  have hI : Continuous (fun q : ℝ ↦ ∫ t in (-(q*L))..(q*L),f t) := by
    have he (q : ℝ) : (∫ t in (-(q*L))..(q*L),f t)=
        (∫ t in (0 : ℝ)..(q*L),f t)-(∫ t in (0 : ℝ)..(-(q*L)),f t) :=
      (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
    simp_rw [he]
    exact (hp.comp (continuous_id.mul_const L)).sub (hp.comp (continuous_id.mul_const L).neg)
  have hc : Continuous (fun q : ℝ ↦ ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))) :=
    ENNReal.continuous_ofReal.comp (((continuous_id.div_const L).mul_const _).add (continuous_const.mul hI))
  have hs : IsClosed {q : ℝ | ENNReal.ofReal (q/L*volume.real A+2*(∫ t in (-(q*L))..(q*L),f t))≤planarTorusPerimeter A} :=
    isClosed_le hc continuous_const
  have h1 : (1 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]; exact ⟨by norm_num,le_rfl⟩
  have hh := closure_minimal (fun q hq ↦ hb q hq) hs h1
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-(1*L))..(1*L),f t))≤planarTorusPerimeter A at hh
  simp only [one_mul] at hh
  change ENNReal.ofReal (1/L*volume.real A+2*(∫ t in (-L)..L,Real.sqrt (1-(t/L)^2)))≤_ at hh
  rw [integral_scaled_semicircle hL.1] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarAxisPoint_continuous : Continuous planarAxisPoint := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact AddCircle.continuous_mk' (1 : ℝ)

lemma planar_axis_can_grow {A : Set TransverseProduct} (hA : IsOpen A)
    {t : ℝ} (ht : t<1/2) (hm : planarAxisPoint t∈A) :
    ∃ s : ℝ,t < s ∧ s<1/2 ∧ planarAxisPoint s∈A := by
  have ho : IsOpen (planarAxisPoint ⁻¹' A ∩ Iio (1/2 : ℝ)) :=
    (hA.preimage planarAxisPoint_continuous).inter isOpen_Iio
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho t ⟨hm,ht⟩
  have he : t+ε/2∈Metric.ball t ε := by
    rw [Metric.mem_ball,Real.dist_eq]
    have hp : 0<ε/2 := half_pos hε
    rw [show t+ε/2-t=ε/2 by ring,abs_of_pos hp]
    linarith
  exact ⟨t+ε/2,by linarith,(hball he).2,(hball he).1⟩

lemma axisCircle_norm_le_half (z : AxisCircle) : ‖z‖≤1/2 := by
  simpa using AddCircle.norm_le_half_period 1 (x := z) (by norm_num)

lemma axisCircle_norm_coe_small {t : ℝ} (ht : |t|≤1/2) : ‖(t : AxisCircle)‖=|t| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
  simpa using ht

theorem planar_radial_extent {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      (∀ t : ℝ,|t|<L →∀ y : TransverseProduct,y 0=0 →y 1=(t : AxisCircle) →y∈A) := by
  let T : Set ℝ := {t | t∈Icc 0 (1/2) ∧ planarAxisPoint t∈A}
  have he0 : planarAxisPoint 0=(0 : TransverseProduct) := by ext j; fin_cases j <;> simp [planarAxisPoint]
  have hzero : planarAxisPoint 0∈A := he0 ▸ h0
  have hne : T.Nonempty := ⟨0,⟨by constructor <;> norm_num,hzero⟩⟩
  have hb : BddAbove T := ⟨1/2,fun t ht ↦ ht.1.2⟩
  let L : ℝ := sSup T
  have hLhalf : L≤1/2 := csSup_le hne (fun t ht ↦ ht.1.2)
  have hcl : planarAxisPoint L∈closure A := by
    exact closure_minimal (s := T) (t := planarAxisPoint ⁻¹' closure A)
      (fun t ht ↦ subset_closure ht.2)
      (isClosed_closure.preimage planarAxisPoint_continuous) (csSup_mem_closure hne hb)
  have hLlt : L<1/2 := lt_of_le_of_ne hLhalf (fun he ↦ hout (he ▸ hcl))
  obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (by norm_num : (0 : ℝ)<1/2) hzero
  have hsL : s≤L := le_csSup hb ⟨⟨hs.le,hsH.le⟩,hsA⟩
  refine ⟨L,⟨hs.trans_le hsL,hLlt⟩,?_,?_⟩
  · intro y hy
    have hp : planarAxisPoint ‖y 1‖∈A := by
      apply hd _ y _ hy
      intro j
      fin_cases j
      · simp [planarAxisPoint]
      · change ‖((‖y 1‖ : ℝ) : AxisCircle)‖≤‖y 1‖
        rw [axisCircle_norm_coe_small (by simpa only [abs_norm] using axisCircle_norm_le_half (y 1)),abs_norm]
    have hrL : ‖y 1‖≤L := le_csSup hb ⟨⟨norm_nonneg _,axisCircle_norm_le_half _⟩,hp⟩
    obtain ⟨s,hs,hsH,hsA⟩ := planar_axis_can_grow hA (hrL.trans_lt hLlt) hp
    exact hs.trans_le (le_csSup hb ⟨⟨(norm_nonneg _).trans hs.le,hsH.le⟩,hsA⟩)
  · intro t ht y hy0 hy1
    obtain ⟨s,hs,hst⟩ := exists_lt_of_lt_csSup hne ht
    apply hd y (planarAxisPoint s) _ hs.2
    intro j
    fin_cases j
    · simp [planarAxisPoint,hy0]
    · change ‖y 1‖≤‖(s : AxisCircle)‖
      rw [hy1,axisCircle_norm_coe_small (ht.le.trans hLhalf),
        axisCircle_norm_coe_small (by simpa [abs_of_nonneg hs.1.1] using hs.1.2),abs_of_nonneg hs.1.1]
      exact hst.le

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

lemma planar_radial_empty_fiber {A : Set TransverseProduct} (hd : PlanarRadialDownset A)
    (hout : planarFirstAxisPoint (1/2)∉closure A) :
    ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A := by
  let f : TransverseProduct →TransverseProduct := fun y ↦ ![y 0,0]
  have hc : Continuous f := by
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 0
    · exact continuous_const
  have hm : A⊆f ⁻¹' closure A := by
    intro y hy
    apply subset_closure
    apply hd (f y) y _ hy
    intro j
    fin_cases j <;> simp [f]
  have hcl := closure_minimal hm (isClosed_closure.preimage hc)
  intro y hy hya
  apply hout
  have he : f y=planarFirstAxisPoint (1/2) := by
    ext j
    fin_cases j <;> simp [f,planarFirstAxisPoint,hy]
  exact he ▸ hcl hya

theorem planar_radial_calibration {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  obtain ⟨L,hL,hband,hin⟩ := planar_radial_extent hA hd h0 hout1
  refine ⟨L,hL,hband,planarTorusPerimeter_ge_semicircle_calibration hA hL ?_ hin
    (planar_radial_empty_fiber hd hout0)⟩
  intro y hy
  obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
  exact ⟨t,ht ▸ hband y hy,he⟩

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_extent_perimeter_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E)) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle),‖y 1‖<L) ∧
      ENNReal.ofReal (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))/L+Real.pi*L)≤
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
  have hp := planar_radial_calibration (centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _)
    (isMinimizerAt_centered_section_radial hV hmin hR hd i _) hzero hv0 hv1
  simpa only [centeredAxialSlice_volume,centeredAxialSlice_perimeter] using hp

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_section_extent_perimeter_oai := @OAI.CubicTorus.isMinimizerAt_section_extent_perimeter_oai
