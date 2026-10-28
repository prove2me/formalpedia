-- Prove2me | solution 1 for OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:00:13.116913+00:00
-- url     : https://prove2.me/submissions/48425913-723a-40b4-a3f9-7f270002906d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_circle_phase
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

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

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

namespace CubicTorus

lemma abs_directional_flux_le {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f x a|
      ≤ ‖a‖ * (perimeter E).toReal := by
  by_cases ha : a = 0
  · simp [ha]
  have hd := hf.differentiable (by simp)
  have hfield : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • a) := hf.smul_const a
  have hfieldp : ∀ n x, f (x + latticeVector n) • a = f x • a := by
    intro n x
    rw [hp]
  have hfieldb : ∀ x, ‖f x • a‖ ≤ ‖a‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg a) (hb x)
  simpa only [divergence_smul_const hd.differentiableAt] using
    abs_flux_le_mul_perimeter hE hfield hfieldp (norm_pos_iff.mpr ha) hfieldb

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

lemma measurableSet_stripe (V : ℝ) : MeasurableSet (stripe V) := by
  apply measurableSet_lt _ measurable_const
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma stripe_lift_preimage {V : ℝ} (hV : V ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' stripe V) =
      univ.pi (fun i : Fin 3 => Ico 0 (stripeUpper V i)) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) < V) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) = x 0 :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc 0)
    rw [he] at hs
    by_cases hi : i = 0
    · subst i
      simpa [stripeUpper] using And.intro (hc 0).1 hs
    · simpa [stripeUpper, hi] using hc i
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := by
      intro i
      have hh := hx i (mem_univ i)
      by_cases hi : i = 0
      · subst i
        simp only [stripeUpper, Function.update_self, mem_Ico] at hh
        exact ⟨hh.1, lt_of_lt_of_le hh.2 hV.2⟩
      · simpa [stripeUpper, hi] using hh
    refine ⟨hc, ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc 0)]
    simpa [stripeUpper] using (hx 0 (mem_univ 0)).2

lemma volume_stripe {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (stripe V) = ENNReal.ofReal V := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_stripe V),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_stripe V)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter (measurable_quotientMap (measurableSet_stripe V))).nullMeasurableSet)
  rw [stripe_lift_preimage hV] at hm
  rw [← hm, Real.volume_pi_Ico]
  norm_num [stripeUpper, Fin.prod_univ_succ]

lemma integral_divergence_stripe {V : ℝ} (hV : V ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' stripe V, divergence F x) =
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let b := stripeUpper V
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
  have hb : ∀ i, (0 : Fin 3 → ℝ) i ≤ b i := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [b, stripeUpper] using hV.1
    · simp [b, stripeUpper, hi]
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) b hb g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : ∀ i : Fin 3, i ≠ 0 →
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth (b i) x)) -
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth 0 x)) = 0 := by
    intro i hi
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth (b i) x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      have hbi : b i = 1 := by simp [b, stripeUpper, hi]
      rw [hbi]
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  simp only [Pi.zero_apply] at hth
  rw [Finset.sum_eq_single 0 (fun i _ hi => hzero i hi) (by simp)] at hth
  have hab : b ∘ (0 : Fin 3).succAbove = (1 : Fin 2 → ℝ) := by
    ext i
    simp [b, stripeUpper]
  have ha0 : (0 : Fin 3 → ℝ) ∘ (0 : Fin 3).succAbove = (0 : Fin 2 → ℝ) := rfl
  rw [hab, ha0] at hth
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, stripe_lift_preimage hV]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  rw [← volume_pi]
  convert hth using 1 <;> simp [g, b, stripeUpper, e]
  rfl

end CubicTorus

namespace CubicTorus

lemma volume_square_face : volume (Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  norm_num

lemma stripe_flux_bound {F : Cover → Cover} (hF : AdmissibleField F) (a : ℝ) :
    |∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x)) 0| ≤ 1 := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (0 : Fin 2 → ℝ) 1) < ⊤ by rw [volume_square_face]; norm_num)
    (fun x (_ : x ∈ Icc (0 : Fin 2 → ℝ) 1) =>
      (PiLp.norm_apply_le (F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x))) 0).trans (hF.2.2 _))
  simpa only [Real.norm_eq_abs, Measure.real, volume_square_face, ENNReal.toReal_one, mul_one] using hh

theorem perimeter_stripe_le {V : ℝ} (hV : V ∈ Icc 0 1) : perimeter (stripe V) ≤ 2 := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [integral_divergence_stripe hV hF]
  have hupper := (abs_le.1 (stripe_flux_bound hF V)).2
  have hlower := (abs_le.1 (stripe_flux_bound hF 0)).1
  have hh : (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) ≤ 2 := by linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by norm_num)

theorem finitePerimeter_stripe {V : ℝ} (hV : V ∈ Icc 0 1) : FinitePerimeter (stripe V) :=
  ⟨(measurableSet_stripe V).nullMeasurableSet, (perimeter_stripe_le hV).trans_lt (by norm_num)⟩

end CubicTorus

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

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma intervalSmoothHat_sum (b : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t) =
      intervalSmoothHat b (u 0) (u n) t := by
  induction n with
  | zero => simp [intervalSmoothHat]
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [intervalSmoothHat]; ring

lemma partitionSmoothTest_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (u σ : ℕ → ℝ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (partitionSmoothTest b u σ n) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (intervalSmoothHat_contDiff hb _ _)

lemma partitionSmoothTest_deriv {b : ℝ → ℝ} (hb : Continuous b)
    (u σ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    deriv (partitionSmoothTest b u σ n) t =
      ∑ i ∈ Finset.range n, σ i * (b (t-u i)-b (t-u (i+1))) := by
  have he : partitionSmoothTest b u σ n =
      ∑ i ∈ Finset.range n, (fun y ↦ σ i*intervalSmoothHat b (u i) (u (i+1)) y) := by
    ext y
    simp [partitionSmoothTest]
  rw [he]
  exact (HasDerivAt.sum (u := Finset.range n) (fun i _ ↦
    (intervalSmoothHat_hasDerivAt hb (u i) (u (i+1)) t).const_mul (σ i))).deriv

lemma partitionSmoothTest_bound {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hσ : ∀ i, |σ i| ≤ 1) (n : ℕ) (t : ℝ) :
    |partitionSmoothTest b u σ n t| ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |σ i*intervalSmoothHat b (u i) (u (i+1)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t := by
      apply Finset.sum_le_sum
      intro i _
      have hh := intervalSmoothHat_nonneg hb hb0 (hu (Nat.le_succ i)) t
      rw [abs_mul,abs_of_nonneg hh]
      exact mul_le_of_le_one_left hh (hσ i)
    _ = intervalSmoothHat b (u 0) (u n) t := intervalSmoothHat_sum _ _ _ _
    _ ≤ 1 := intervalSmoothHat_le_one hb hbi hb0 hb1 (hu (Nat.zero_le n)) t

lemma partitionSmoothTest_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hus : ∀ i, u i ∈ Icc a c) (n : ℕ) :
    tsupport (partitionSmoothTest b u σ n) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  apply Finset.sum_eq_zero
  intro i _
  have hn : t ∉ tsupport (intervalSmoothHat b (u i) (u (i+1))) := by
    intro h
    have H := intervalSmoothHat_support hb hs (hu (Nat.le_succ i)) h
    exact hh ⟨by linarith [(hus i).1,H.1],by linarith [(hus (i+1)).2,H.2]⟩
  rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]

lemma bounded_mul_shift_integrable {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hbi : Integrable b volume) (x : ℝ) :
    Integrable (fun t ↦ f t*b (t-x)) volume := by
  have hi : Integrable (fun t ↦ b (t-x)) volume := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      ((measurePreserving_add_right volume (-x)).integrable_comp hbi.aestronglyMeasurable).mpr hbi
  apply hi.norm.mono' (hf.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  apply ae_of_all
  intro t
  change |f t*b (t-x)| ≤ |b (t-x)|
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hf1 t)

lemma partitionSmoothTest_flux {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hb : Continuous b) (hbi : Integrable b volume)
    (u σ : ℕ → ℝ) (n : ℕ) :
    (∫ t : ℝ, f t*deriv (partitionSmoothTest b u σ n) t) =
      ∑ i ∈ Finset.range n, σ i*((∫ t : ℝ, f t*b (t-u i))-
        ∫ t : ℝ, f t*b (t-u (i+1))) := by
  simp_rw [partitionSmoothTest_deriv hb,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simp_rw [show ∀ t : ℝ, f t*(σ i*(b (t-u i)-b (t-u (i+1)))) =
      σ i*(f t*b (t-u i)-f t*b (t-u (i+1))) by intro t; ring]
    rw [integral_const_mul,integral_sub (bounded_mul_shift_integrable hf hf1 hbi _)
      (bounded_mul_shift_integrable hf hf1 hbi _)]
  · intro i _
    convert ((bounded_mul_shift_integrable hf hf1 hbi (u i)).sub
      (bounded_mul_shift_integrable hf hf1 hbi (u (i+1)))).const_mul (σ i) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp only [Pi.sub_apply]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma angularMollifier_radius_tendsto :
    Tendsto (fun n ↦ (angularMollifier n).rOut) atTop (𝓝 0) := by
  have he (n : ℕ) : (angularMollifier n).rOut = (1/8 : ℝ)*(1/((n : ℝ)+1)) := by
    dsimp [angularMollifier]; field_simp; ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_const_nhds (x := (1/8 : ℝ))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma angular_smoothing_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) :
    ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun n ↦ ∫ t : ℝ, f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x)) := by
  have hli : LocallyIntegrable f volume := by
    apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono
      hf.aestronglyMeasurable
    exact ae_of_all _ (fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hf1 t)
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    angularMollifier_radius_tendsto (K := 2)
    (Eventually.of_forall fun n ↦ by dsimp [angularMollifier]; ring_nf; rfl) hli
  filter_upwards [ht] with x hx
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change f t*(angularMollifier n).normed volume (t-x) =
      (angularMollifier n).normed volume (x-t)*f t
  rw [show x-t = -(t-x) by ring,(angularMollifier n).normed_neg]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

namespace CubicTorus.UpperComparison

lemma fieldMove_hasFDerivAt {F : Cover → Cover} {x : Cover}
    (hf : DifferentiableAt ℝ F x) (t : ℝ) :
    HasFDerivAt (fieldMove F t) (fieldMoveDeriv F t x) x :=
  (hasFDerivAt_id x).add (hf.hasFDerivAt.const_smul t)

lemma fieldMoveDeriv_det (F : Cover → Cover) (t : ℝ) (x : Cover) :
    (fieldMoveDeriv F t x).det =
      1 + t * divergence F x + t ^ 2 * secondJacobian F x + t ^ 3 * thirdJacobian F x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (fieldMoveDeriv F t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) + t * derivativeEntry F x j k) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (fieldMoveDeriv F t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    simp [fieldMoveDeriv, derivativeEntry]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  simp [Matrix.det_fin_three, divergence, secondJacobian, thirdJacobian,
    derivativeEntry, Fin.sum_univ_succ]
  ring

lemma fieldMove_injective {F : Cover → Cover} (hf : Differentiable ℝ F)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M) {t : ℝ}
    (ht : |t| * M < 1) : Function.Injective (fieldMove F t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = (-t) • (F x - F y) := by
    calc
      x - y = fieldMove F t x - fieldMove F t y - t • (F x - F y) := by
        unfold fieldMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖F x - F y‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    calc
      ‖x - y‖ = |t| * ‖F x - F y‖ := hn
      _ ≤ |t| * ((M : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

lemma continuous_derivativeEntry {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) : Continuous (fun x ↦ derivativeEntry F x i j) := by
  exact (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma continuous_secondJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (secondJacobian F) := by
  unfold secondJacobian
  exact (((((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 1 1)).add
    ((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 2 2))).add
    ((continuous_derivativeEntry hf 1 1).mul (continuous_derivativeEntry hf 2 2))).sub
    ((continuous_derivativeEntry hf 0 1).mul (continuous_derivativeEntry hf 1 0))).sub
    ((continuous_derivativeEntry hf 0 2).mul (continuous_derivativeEntry hf 2 0)) |>.sub
    ((continuous_derivativeEntry hf 1 2).mul (continuous_derivativeEntry hf 2 1))

lemma continuous_thirdJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (thirdJacobian F) := by
  exact (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_derivativeEntry hf i j).matrix_det

lemma integral_det_fieldMove {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    {A : Set Cover} (hAc : IsCompact (closure A)) (t : ℝ) :
    (∫ x in A, (fieldMoveDeriv F t x).det) = volume.real A +
      t * (∫ x in A, divergence F x) + t ^ 2 * (∫ x in A, secondJacobian F x) +
      t ^ 3 * (∫ x in A, thirdJacobian F x) := by
  have h1 : IntegrableOn (divergence F) (closure A) volume :=
    (continuous_divergence hf).continuousOn.integrableOn_compact hAc
  have h2 : IntegrableOn (secondJacobian F) (closure A) volume :=
    (continuous_secondJacobian hf).continuousOn.integrableOn_compact hAc
  have h3 : IntegrableOn (thirdJacobian F) (closure A) volume :=
    (continuous_thirdJacobian hf).continuousOn.integrableOn_compact hAc
  have hμ : volume A < ⊤ := (measure_mono subset_closure).trans_lt hAc.measure_lt_top
  have hc : IntegrableOn (fun _ : Cover ↦ (1 : ℝ)) A :=
    integrableOn_const hμ.ne
  simp_rw [fieldMoveDeriv_det]
  rw [integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x + t^2 * secondJacobian F x)
      (g := fun x ↦ t^3 * thirdJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        ((hc.add ((h1.mono_set subset_closure).const_mul t)).add
          ((h2.mono_set subset_closure).const_mul (t^2))))
      ((h3.mono_set subset_closure).const_mul (t^3)),
    integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x)
      (g := fun x ↦ t^2 * secondJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        (hc.add ((h1.mono_set subset_closure).const_mul t)))
      ((h2.mono_set subset_closure).const_mul (t^2)),
    integral_add (μ := volume.restrict A) (f := fun _ : Cover ↦ (1 : ℝ)) (g := fun x ↦ t * divergence F x)
      hc ((h1.mono_set subset_closure).const_mul t)]
  simp only [integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma integral_det_fieldMove_le_volume {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {A : Set Cover} (hA : MeasurableSet A)
    (hAc : IsCompact (closure A)) :
    (∫ x in A, (fieldMoveDeriv F t x).det) ≤ volume.real (fieldMove F t '' A) := by
  have hdet : Continuous (fun x ↦ (fieldMoveDeriv F t x).det) :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add ((hf.continuous_fderiv (by simp)).const_smul t))
  have hi : IntegrableOn (fun x ↦ (fieldMoveDeriv F t x).det) A volume :=
    (hdet.continuousOn.integrableOn_compact hAc).mono_set subset_closure
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume hA
    (fun x (_ : x ∈ A) ↦
      (fieldMove_hasFDerivAt (hf.differentiable (by simp) x) t).hasFDerivWithinAt)
    (fieldMove_injective (hf.differentiable (by simp)) hM ht).injOn (fun _ ↦ (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hj
  rw [hj]
  exact integral_mono hi hi.abs (fun x ↦ le_abs_self _)

lemma realVolume_cover_ball (c : Cover) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball c r) = r ^ 3 * (Real.pi * 4 / 3) := by
  simp only [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.pi * 4 / 3)]

lemma fieldMove_ball_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (c : Cover) (r : ℝ) :
    fieldMove F t '' Metric.ball c r ⊆ Metric.ball c (r + t) := by
  rintro _ ⟨x, hx, rfl⟩
  have hh : ‖t • F x‖ ≤ t := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
      mul_le_mul_of_nonneg_left (hF x) ht
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  calc
    ‖fieldMove F t x - c‖ = ‖(x - c) + t • F x‖ := by congr 1; unfold fieldMove; abel
    _ ≤ ‖x - c‖ + ‖t • F x‖ := norm_add_le _ _
    _ < r + t := add_lt_add_of_lt_of_le hx hh

lemma flux_cover_ball_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (c : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball c r, divergence F x) ≤ 4 * Real.pi * r ^ 2 := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in Metric.ball c r, divergence F x
  let Q := ∫ x in Metric.ball c r, secondJacobian F x
  let R := ∫ x in Metric.ball c r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M + 1) →
      P + t * Q + t ^ 2 * R ≤
        4 * Real.pi * r ^ 2 + 4 * Real.pi * r * t + (Real.pi * 4 / 3) * t ^ 2 := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t * M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM (A := Metric.ball c r) Metric.isOpen_ball.measurableSet
      (Metric.isBounded_ball.isCompact_closure)
    have hv' : volume.real (fieldMove F t '' Metric.ball c r) ≤
        volume.real (Metric.ball c (r + t)) := by
      exact ENNReal.toReal_mono measure_ball_ne_top (measure_mono (fieldMove_ball_subset hF ht0.le c r))
    rw [integral_det_fieldMove hf Metric.isBounded_ball.isCompact_closure,
      realVolume_cover_ball c hr.le] at hv
    rw [realVolume_cover_ball c (by linarith)] at hv'
    have hh := hv.trans hv'
    change r^3 * (Real.pi*4/3) + t*P + t^2*Q + t^3*R ≤ _ at hh
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t * Q + t^2 * R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t * Q + t^2 * R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
      (Real.pi * 4 / 3) * t^2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Real.pi * r^2)) := by
    have hh : Continuous (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
        (Real.pi * 4 / 3) * t^2) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet (cubeBall r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 1 / 2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeBall r = Metric.ball cubeCenter r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (cubeBall r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

lemma perimeter_cubeBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (cubeBall r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeBall_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_cover_ball_le hF.1 hF.2.1 hF.2.2 cubeCenter hr0)

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

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

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma centeredBall_eq_cubeBall_preimage (r : ℝ) :
    Metric.ball (0 : Torus) r =
      (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeBall r := by
  rw [cubeBall_eq_metricBall]
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

lemma volume_centeredBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball (0 : Torus) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [centeredBall_eq_cubeBall_preimage,
    volume_translation (measurableSet_cubeBall r).nullMeasurableSet, volume_cubeBall hr0 hr1]

lemma perimeter_centeredBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (Metric.ball (0 : Torus) r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  rw [centeredBall_eq_cubeBall_preimage,
    perimeter_translation (measurableSet_cubeBall r).nullMeasurableSet]
  exact perimeter_cubeBall_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma discProjection_norm_le (x : Cover) : ‖discProjection x‖ ≤ ‖x‖ := by
  have hh : ‖discProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [discProjection_apply, Fin.sum_univ_succ]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (discProjection x), norm_nonneg x]

lemma continuous_tubeSplit_symm : Continuous tubeSplit.symm := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).continuous_symm.comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × Plane ↦ tubeSplit.symm p i)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [tubeSplit_symm_zero] using (continuous_fst : Continuous (fun p : ℝ × Plane ↦ p.1))
  · simp_rw [tubeSplit_symm_succ]
    fun_prop

lemma tubeSplit_measurePreserving : MeasurePreserving tubeSplit := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

lemma measurableSet_coverTube (r : ℝ) : MeasurableSet (coverTube r) :=
  (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).preimage tubeSplit.measurable

lemma isCompact_closure_coverTube (r : ℝ) : IsCompact (closure (coverTube r)) := by
  have hc : IsCompact (tubeSplit.symm '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall discCenter r)) :=
    (isCompact_Icc.prod (isCompact_closedBall discCenter r)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨tubeSplit x, ⟨⟨hx.1.1, hx.1.2.le⟩, Metric.ball_subset_closedBall hx.2⟩, ?_⟩
  exact tubeSplit.symm_apply_apply x

lemma volume_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume (coverTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [coverTube, tubeSplit_measurePreserving.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
      EuclideanSpace.volume_ball_fin_two]
    simp only [sub_zero, ENNReal.ofReal_one, one_mul]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr]
    ring
  · exact (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).nullMeasurableSet

lemma volumeReal_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coverTube r) = Real.pi * r^2 := by
  rw [Measure.real_def, volume_coverTube hr, ENNReal.toReal_ofReal (by positivity)]

lemma axialProjection_norm_le (x : Cover) : ‖axialProjection x‖ ≤ ‖x‖ := by
  have hh : ‖axialProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_succ, axialProjection_zero, axialProjection_succ, norm_zero,
      zero_pow (by omega : 2 ≠ 0), zero_add]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (axialProjection x), norm_nonneg x]

lemma fieldMove_coverTube_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    (hF0 : ∀ x, F x 0 = 0) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    fieldMove F t '' coverTube r ⊆ coverTube (r+t) := by
  rintro _ ⟨x, hx, rfl⟩
  change (fieldMove F t x) 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (fieldMove F t x) ∈ Metric.ball discCenter (r+t)
  constructor
  · simpa [fieldMove, hF0 x] using hx.1
  · have hb : ‖discProjection (F x)‖ ≤ 1 := (discProjection_norm_le _).trans (hF x)
    have hh : ‖t • discProjection (F x)‖ ≤ t := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
        mul_le_mul_of_nonneg_left hb ht
    have hd : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      _ = ‖(discProjection x - discCenter) + t • discProjection (F x)‖ := by
        congr 1
        simp only [fieldMove, map_add, map_smul]
        abel
      _ ≤ ‖discProjection x - discCenter‖ + ‖t • discProjection (F x)‖ := norm_add_le _ _
      _ < r+t := add_lt_add_of_lt_of_le hd hh

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma tubeSplit_symm_line (u : ℝ) (y : Plane) :
    tubeSplit.symm (u,y) = tubeSplit.symm (0,y) + u • EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

lemma hasDerivAt_tubeLine (u : ℝ) (y : Plane) :
    HasDerivAt (fun t : ℝ ↦ tubeSplit.symm (t,y)) (EuclideanSpace.single 0 1) u := by
  have he : (fun t : ℝ ↦ tubeSplit.symm (t,y)) =
      (fun t : ℝ ↦ tubeSplit.symm (0,y) + t • EuclideanSpace.single 0 1) :=
    funext (fun t ↦ tubeSplit_symm_line t y)
  rw [he]
  simpa! only [Pi.add_def, zero_add, one_smul, id_eq] using
    (hasDerivAt_const u (tubeSplit.symm (0,y))).add
      ((hasDerivAt_id u).smul_const (EuclideanSpace.single 0 1))

lemma axial_integral_eq_zero {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (y : Plane) :
    (∫ u in Ico (0 : ℝ) 1, derivativeEntry F (tubeSplit.symm (u,y)) 0 0) = 0 := by
  have hd (u : ℝ) : HasDerivAt (fun u ↦ F (tubeSplit.symm (u,y)) 0)
      (derivativeEntry F (tubeSplit.symm (u,y)) 0 0) u := by
    exact (EuclideanSpace.proj 0).hasFDerivAt.comp_hasDerivAt u
      (((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt u
        (hasDerivAt_tubeLine u y))
  have hc : Continuous (fun u ↦ derivativeEntry F (tubeSplit.symm (u,y)) 0 0) :=
    (continuous_derivativeEntry hf 0 0).comp (continuous_tubeSplit_symm.comp (by fun_prop))
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u) (hc.intervalIntegrable 0 1)]
  have he : tubeSplit.symm (1,y) = tubeSplit.symm (0,y) + latticeVector (Pi.single 0 1) := by
    rw [tubeSplit_symm_line 1 y]
    congr 1
    ext i
    simp [latticeVector, Pi.single_apply]
  rw [he, hp]
  simp

lemma integral_axial_coverTube {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, derivativeEntry F x 0 0) = 0 := by
  let g : ℝ × Plane → ℝ := fun p ↦ derivativeEntry F (tubeSplit.symm p) 0 0
  have hint : IntegrableOn (fun x ↦ derivativeEntry F x 0 0) (coverTube r) :=
    ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g, Function.comp_def, tubeSplit.symm_apply_apply, coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  simp only [g, tubeSplit.symm_apply_apply] at he
  change (∫ x in coverTube r, derivativeEntry F x 0 0) = _ at he
  rw [he]
  change (∫ p in Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r, g p) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [integral_prod_symm g hi]
  simp only [g, axial_integral_eq_zero hf hp, integral_zero]

lemma divergence_axialProjection {x : Cover} {F : Cover → Cover} (hf : DifferentiableAt ℝ F x) :
    divergence (fun y ↦ axialProjection (F y)) x = divergence F x - derivativeEntry F x 0 0 := by
  have hc : HasFDerivAt (fun y ↦ axialProjection (F y))
      (axialProjection.comp (fderiv ℝ F x)) x :=
    axialProjection.hasFDerivAt.comp x hf.hasFDerivAt
  simp only [divergence, hc.fderiv, ContinuousLinearMap.comp_apply, Fin.sum_univ_succ,
    axialProjection_zero, axialProjection_succ, derivativeEntry]
  ring

lemma flux_axialProjection {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, divergence (fun y ↦ axialProjection (F y)) x) =
      ∫ x in coverTube r, divergence F x := by
  simp_rw [divergence_axialProjection ((hf.differentiable (by simp)).differentiableAt)]
  rw [integral_sub]
  · rw [integral_axial_coverTube hf hp, sub_zero]
  · exact ((continuous_divergence hf).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  · exact ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma flux_coverTube_axial_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : ∀ x, F x 0 = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in coverTube r, divergence F x
  let Q := ∫ x in coverTube r, secondJacobian F x
  let R := ∫ x in coverTube r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M+1) →
      P + t*Q + t^2*R ≤ 2 * Real.pi * r + Real.pi*t := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t*M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM
      (measurableSet_coverTube r) (isCompact_closure_coverTube r)
    have hfin : volume (coverTube (r+t)) ≠ ⊤ := by
      rw [volume_coverTube (by linarith)]
      exact ENNReal.ofReal_ne_top
    have hv' : volume.real (fieldMove F t '' coverTube r) ≤ volume.real (coverTube (r+t)) :=
      ENNReal.toReal_mono hfin (measure_mono (fieldMove_coverTube_subset hF hF0 ht0.le r))
    rw [integral_det_fieldMove hf (isCompact_closure_coverTube r)] at hv
    rw [volumeReal_coverTube (by linarith : 0 ≤ r+t)] at hv'
    rw [volumeReal_coverTube hr.le] at hv
    change Real.pi*r^2 + t*P + t^2*Q + t^3*R ≤ _ at hv
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith [hv.trans hv']
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t*Q + t^2*R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t*Q + t^2*R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*r)) := by
    have hh : Continuous (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1/(M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

lemma flux_coverTube_le {F : Cover → Cover} (hF : AdmissibleField F)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  rw [← flux_axialProjection hF.1 hF.2.1 r]
  apply flux_coverTube_axial_le (axialProjection.contDiff.comp hF.1)
  · intro n x
    change axialProjection (F (x + latticeVector n)) = axialProjection (F x)
    rw [hF.2.1]
  · intro x
    exact (axialProjection_norm_le _).trans (hF.2.2 x)
  · intro x
    exact axialProjection_zero (F x)
  · exact hr

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma representative_mem_cube (x : Torus) : representative x ∈ fundamentalCube := by
  intro i
  exact ⟨((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.1,
    by simpa! only [representative, PiLp.toLp_apply, zero_add] using
      ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.2⟩

lemma coverTube_subset_cube {r : ℝ} (hr : r ≤ 1/2) : coverTube r ⊆ fundamentalCube := by
  intro x hx i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hx.1
  · have hnorm : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    have hi := (PiLp.norm_apply_le (discProjection x - discCenter) j).trans_lt hnorm
    change |x j.succ - (1/2 : ℝ)| < r at hi
    rw [abs_lt] at hi
    constructor <;> linarith

lemma measurableSet_cubeTube (r : ℝ) : MeasurableSet (cubeTube r) :=
  (measurableSet_coverTube r).preimage measurable_representative

lemma cubeTube_lift {r : ℝ} (hr : r ≤ 1/2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeTube r = coverTube r := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    change representative (quotientMap x) ∈ coverTube r at ht
    rwa [representative_quotientMap_of_mem hx] at ht
  · intro ht
    have hx := coverTube_subset_cube hr ht
    refine ⟨hx, ?_⟩
    change representative (quotientMap x) ∈ coverTube r
    rwa [representative_quotientMap_of_mem hx]

lemma volume_cubeTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (cubeTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeTube r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeTube r)), inter_comm,
    cubeTube_lift hr1, volume_coverTube hr0]

lemma perimeter_cubeTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (cubeTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeTube_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_coverTube_le hF hr0)

lemma norm_representative_sub_half (x : Torus) (i : Fin 3) :
    ‖representative x i - (1/2 : ℝ)‖ = ‖x i - ((1/2 : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hi := representative_mem_cube x i
  have hb : |representative x i - (1/2 : ℝ)| ≤ |(1 : ℝ)|/2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hn : ‖((representative x i - (1/2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1/2 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hb
  have hxi : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i :=
    congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [map_sub, hxi, Real.norm_eq_abs] using hn.symm

lemma mem_cubeTube_iff {r : ℝ} (hr : 0 ≤ r) (x : Torus) :
    x ∈ cubeTube r ↔ x - quotientMap cubeCenter ∈ centeredTube r := by
  change (representative x 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (representative x) ∈ Metric.ball discCenter r) ↔ _
  simp only [mem_Ico]
  rw [and_iff_right (representative_mem_cube x 0), Metric.mem_ball, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) hr, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, discProjection_apply, discCenter,
    norm_representative_sub_half]
  rfl

lemma centeredTube_eq_cubeTube_preimage {r : ℝ} (hr : 0 ≤ r) :
    centeredTube r = (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeTube r := by
  ext x
  simp only [mem_preimage, mem_cubeTube_iff hr, add_sub_cancel_right]

lemma measurableSet_centeredTube (r : ℝ) : MeasurableSet (centeredTube r) := by
  apply measurableSet_lt
  · fun_prop
  · fun_prop

lemma volume_centeredTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (centeredTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [centeredTube_eq_cubeTube_preimage hr0,
    volume_translation (measurableSet_cubeTube r).nullMeasurableSet,
    volume_cubeTube hr0 hr1]

lemma perimeter_centeredTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (centeredTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  rw [centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (measurableSet_cubeTube r).nullMeasurableSet]
  exact perimeter_cubeTube_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma cube_cuberoot (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

lemma cube_two_thirds (x : ℝ) (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma canonicalBall_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < (3*V/(4*Real.pi))^(1/3 : ℝ) ∧
    (3*V/(4*Real.pi))^(1/3 : ℝ) ≤ 1/2 ∧
    ((3*V/(4*Real.pi))^(1/3 : ℝ))^3 * (Real.pi*4/3) = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  have hv : 0 < 3*V/(4*Real.pi) := by positivity
  have hc := cube_cuberoot _ hv.le
  refine ⟨Real.rpow_pos_of_pos hv _, ?_, ?_⟩
  · have hbound : 3*V/(4*Real.pi) ≤ (1/2 : ℝ)^3 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
      nlinarith [Real.pi_gt_three, hV.2]
    have hp3 : Odd (3 : ℕ) := by decide
    apply hp3.strictMono_pow.le_iff_le.1
    rw [hc]
    exact hbound
  · rw [hc]
    field_simp

lemma ballArea_formula {V : ℝ} (hV : 0 ≤ V) :
    4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2 =
      (36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
  apply (show Odd (3 : ℕ) by decide).pow_injective
  have hc := cube_cuberoot (3*V/(4*Real.pi)) (by positivity)
  have hpc := cube_cuberoot (36*Real.pi) (by positivity)
  have hvc := cube_two_thirds V hV
  dsimp only
  calc
    (4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2)^3 =
        (4*Real.pi)^3 * (((3*V/(4*Real.pi))^(1/3 : ℝ))^3)^2 := by ring
    _ = 36*Real.pi*V^2 := by rw [hc]; field_simp; ring
    _ = _ := by rw [mul_pow, hpc, hvc]

lemma volume_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalBall V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalBall_radius_properties hV
  change torusVolume (Metric.ball (0 : Torus) _) = _
  rw [volume_centeredBall hr0.le hr1, heq]

lemma perimeter_canonicalBall_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalBall V) ≤
      ENNReal.ofReal ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalBall_radius_properties hV
  exact (perimeter_centeredBall_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (ballArea_formula hV.1.le))

lemma finitePerimeter_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalBall V) :=
  ⟨Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    (perimeter_canonicalBall_le hV).trans_lt ENNReal.ofReal_lt_top⟩

lemma canonicalTube_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < Real.sqrt (V/Real.pi) ∧ Real.sqrt (V/Real.pi) ≤ 1/2 ∧
    Real.pi * (Real.sqrt (V/Real.pi))^2 = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  refine ⟨Real.sqrt_pos.2 (div_pos hV.1 hp), ?_, ?_⟩
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_gt_three, hV.2]
  · rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma tubeArea_formula {V : ℝ} (hV : 0 ≤ V) :
    2*Real.pi*Real.sqrt (V/Real.pi) = 2*Real.sqrt (Real.pi*V) := by
  have hp := Real.pi_pos
  have heq : Real.pi*Real.sqrt (V/Real.pi) = Real.sqrt (Real.pi*V) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  calc
    _ = 2*(Real.pi*Real.sqrt (V/Real.pi)) := by ring
    _ = _ := by rw [heq]

lemma volume_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalTube V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalTube_radius_properties hV
  change torusVolume (centeredTube _) = _
  rw [volume_centeredTube hr0.le hr1, heq]

lemma perimeter_canonicalTube_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V) ≤ ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalTube_radius_properties hV
  exact (perimeter_centeredTube_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (tubeArea_formula hV.1.le))

lemma finitePerimeter_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalTube V) :=
  ⟨(measurableSet_centeredTube _).nullMeasurableSet,
    (perimeter_canonicalTube_le hV).trans_lt ENNReal.ofReal_lt_top⟩

theorem isMinimizerAt_perimeter_le_envelope {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal
      (min ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ))
        (min (2*Real.sqrt (Real.pi*V)) 2)) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_min]
  refine le_min ?_ (le_min ?_ ?_)
  · exact (hE.2.2 _ (finitePerimeter_canonicalBall hV) (volume_canonicalBall hV)).trans
      (perimeter_canonicalBall_le hV)
  · exact (hE.2.2 _ (finitePerimeter_canonicalTube hV) (volume_canonicalTube hV)).trans
      (perimeter_canonicalTube_le hV)
  · have hVI : V ∈ Icc (0 : ℝ) 1 := ⟨hV.1.le, by linarith [hV.2]⟩
    simpa only [ENNReal.ofReal_ofNat] using
      (hE.2.2 _ (finitePerimeter_stripe hVI) (volume_stripe hVI)).trans (perimeter_stripe_le hVI)

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) := by
  by_cases hhalf : V ≤ 1/2
  · simpa only [candidateProfile, min_eq_left (by linarith : V ≤ 1-V)] using
      isMinimizerAt_perimeter_le_envelope ⟨hV.1, hhalf⟩ hE
  · have hvol : 1-V ∈ Ioc (0 : ℝ) (1/2) := ⟨by linarith [hV.2], by linarith⟩
    have hcompl := (isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hE
    have hh := isMinimizerAt_perimeter_le_envelope hvol hcompl
    simpa only [perimeter_compl hE.1.1, candidateProfile,
      min_eq_right (by linarith : 1-V ≤ V)] using hh

end CubicTorus.UpperComparison

namespace CubicTorus

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) :=
  UpperComparison.isMinimizerAt_perimeter_le_candidateProfile hV hE

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

lemma continuous_integerCharacter (m : Fin 3 → ℤ) : Continuous (integerCharacter m) := by
  change Continuous (fun x : Torus ↦ ∑ i,m i • x i)
  exact continuous_finsetSum Finset.univ fun i _ ↦
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ)) i).zsmul (m i)

lemma integerCharacter_quotientMap (m : Fin 3 → ℤ) (x : Cover) :
    integerCharacter m (quotientMap x)=(⟪latticeVector m,x⟫ : AddCircle (1 : ℝ)) := by
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=_
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,latticeVector,WithLp.ofLp_toLp]
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (∑ i,x i*(m i : ℝ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,← zsmul_eq_mul]
  rfl

lemma integerCharacter_surjective {m : Fin 3 → ℤ} (hm : m≠0) :
    Function.Surjective (integerCharacter m) := by
  have hi : ∃ i,m i≠0 := by
    by_contra hn
    push Not at hn
    exact hm (funext hn)
  obtain ⟨i,hi⟩ := hi
  intro z
  let t : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z).1
  refine ⟨quotientMap (EuclideanSpace.single i (t/(m i : ℝ))),?_⟩
  rw [integerCharacter_quotientMap,EuclideanSpace.inner_single_right]
  simp only [latticeVector,WithLp.ofLp_toLp,starRingEnd_apply,star_trivial]
  rw [div_mul_cancel₀ t (by exact_mod_cast hi)]
  exact AddCircle.coe_equivIco

theorem integerCharacter_measurePreserving {m : Fin 3 → ℤ} (hm : m≠0) :
    MeasurePreserving (integerCharacter m) torusVolume volume := by
  have hc := continuous_integerCharacter m
  let : (Measure.map (integerCharacter m) torusVolume).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure torusVolume (integerCharacter m) hc
      (integerCharacter_surjective hm)
  let : IsProbabilityMeasure (Measure.map (integerCharacter m) torusVolume) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  refine ⟨hc.measurable,?_⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

theorem integerCharacter_directional_variation {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K) ≠ ⊤)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : Function.Periodic ψ 1) (hb : ∀ t,|ψ t|≤1) (a : ℝ) :
    ‖latticeVector m‖ * |∫ t in a..a+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))| ≤
      (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  let n := latticeVector m
  let l : Cover →L[ℝ] ℝ := innerSL ℝ n
  let f : Cover → ℝ := fun x ↦ ψ (l x)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp l.contDiff
  have hper : ∀ z x,f (x+latticeVector z)=f x := by
    intro z x
    change ψ (⟪n,x+latticeVector z⟫)=ψ ⟪n,x⟫
    rw [inner_add_right]
    have he : ⟪n,latticeVector z⟫ = (∑ i,m i*z i : ℤ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct,star_trivial,n,latticeVector,WithLp.ofLp_toLp,Int.cast_sum,Int.cast_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    simpa only [mul_one] using hp.int_mul (∑ i,m i*z i) ⟪n,x⟫
  have hdir := abs_directional_flux_le hP hf hper (fun x ↦ hb (l x)) n
  have hd (x : Cover) : fderiv ℝ f x n=deriv ψ ⟪n,x⟫*‖n‖^2 := by
    have hh := ((hψ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt
      x l.hasFDerivAt
    change (fderiv ℝ (ψ ∘ l) x) n=_
    rw [hh.fderiv]
    simp only [smul_apply,smul_eq_mul,l,innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq]
  simp_rw [hd] at hdir
  rw [integral_mul_const,abs_mul,abs_of_nonneg (sq_nonneg ‖n‖)] at hdir
  let g : AddCircle (1 : ℝ) → ℝ := K.indicator (real_periodic_deriv hp).lift
  have hg : Measurable g := (continuous_periodic_lift (real_periodic_deriv hp)
    (hψ.continuous_deriv (by simp))).measurable.indicator hK
  have hint : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K),
      deriv ψ ⟪n,x⟫) = ∫ t in a..a+1,g (t : AddCircle (1 : ℝ)) := by
    rw [← lift_indicator_integral (hK.preimage (continuous_integerCharacter m).measurable).nullMeasurableSet]
    have he (x : Cover) : (quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K)).indicator
        (fun x ↦ deriv ψ ⟪n,x⟫) x = g (integerCharacter m (quotientMap x)) := by
      by_cases hx : integerCharacter m (quotientMap x)∈K
      · rw [Set.indicator_of_mem (show x∈quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K) from hx)]
        change _=K.indicator (real_periodic_deriv hp).lift (integerCharacter m (quotientMap x))
        rw [Set.indicator_of_mem hx,integerCharacter_quotientMap]
        rfl
      · rw [Set.indicator_of_notMem (show x∉quotientMap ⁻¹' ((integerCharacter m) ⁻¹' K) from hx)]
        exact (Set.indicator_of_notMem hx _).symm
    simp_rw [he]
    have hh := integral_map (μ := volume.restrict fundamentalCube) quotientMap_measurePreserving.measurable.aemeasurable
      (hg.comp (continuous_integerCharacter m).measurable).aestronglyMeasurable
    rw [quotientMap_measurePreserving.map_eq] at hh
    simp only [Function.comp_apply] at hh
    rw [← hh]
    have hh' := integral_map (μ := torusVolume) (integerCharacter_measurePreserving hm).measurable.aemeasurable
      (show AEStronglyMeasurable g (Measure.map (integerCharacter m) torusVolume) from
        hg.aestronglyMeasurable)
    rw [(integerCharacter_measurePreserving hm).map_eq] at hh'
    rw [← hh',AddCircle.intervalIntegral_preimage]
  rw [hint] at hdir
  have hn : 0<‖n‖ := by
    apply norm_pos_iff.mpr
    intro hn
    apply hm
    funext i
    have hi := congrArg (fun x : Cover ↦ x i) hn
    simp only [n,latticeVector,WithLp.ofLp_toLp,PiLp.zero_apply] at hi
    exact_mod_cast hi
  nlinarith [abs_nonneg (∫ t in a..a+1,g (t : AddCircle (1 : ℝ)))]

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_hat_calibration {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c)
    (hshort : c-a+2*r<1) :
    2*‖latticeVector m‖ * |(∫ t : ℝ, K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*b (t-a))-
      ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*b (t-c)| ≤
        (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := ((measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable)
  have hf1 (t : ℝ) : |f t|≤1 := by simp only [f,Set.indicator_apply]; split_ifs <;> norm_num
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H := by
    apply IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
    exact (intervalSmoothHat_support hb.continuous hs hac)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := intervalSmoothHat_contDiff hb a c
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff hH hHc)).sub contDiff_const
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
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*deriv H t := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff hH hHc).differentiable (by simp) t),he.deriv_eq]
  have hint : (∫ t in (d-1/2)..(d-1/2)+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ)))=
      2*((∫ t : ℝ,f t*b (t-a))-∫ t : ℝ,f t*b (t-c)) := by
    rw [show d-1/2+1=d+1/2 by ring]
    have hi : (∫ t in (d-1/2)..d+1/2,f t*deriv H t)=∫ t : ℝ,f t*deriv H t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hn : t∉tsupport H := by
        intro hh
        exact ht ⟨(hHs hh).1,(hHs hh).2.le⟩
      rw [deriv_of_notMem_tsupport hn,mul_zero]
    calc
      _ = 2*(∫ t in (d-1/2)..d+1/2,f t*deriv H t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t∈Icc (d-1/2) (d+1/2) := by
          simpa only [uIcc_of_le (show d-1/2≤d+1/2 by linarith)] using ht
        change K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))=2*(f t*deriv H t)
        by_cases hk : (t : AddCircle (1 : ℝ))∈K
        · rw [Set.indicator_of_mem hk]
          change deriv ψ t=2*(K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t)
          rw [Set.indicator_of_mem hk,one_mul,hd t ht']
        · rw [Set.indicator_of_notMem hk]
          change 0=2*(K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t)
          rw [Set.indicator_of_notMem hk,zero_mul,mul_zero]
      _ = _ := by
        rw [hi]
        have he (t : ℝ) : deriv H t=b (t-a)-b (t-c) :=
          (intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv
        simp_rw [he,mul_sub]
        rw [integral_sub (bounded_mul_shift_integrable hf hf1 hbi a)
          (bounded_mul_shift_integrable hf hf1 hbi c)]
        ring
  have hh := integerCharacter_directional_variation hm hK hP hψ hp hbψ (d-1/2)
  rw [hint,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_nontrivial_phase_lower_bound {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hpos : volume K≠0) (hneg : volume Kᶜ≠0)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤) :
    2*‖latticeVector m‖ ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := (measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable
  have hf1 (t : ℝ) : |f t|≤1 := by
    simp only [f,Set.indicator_apply]
    split_ifs <;> norm_num
  let G (x : ℝ) := Tendsto
    (fun n ↦ ∫ t : ℝ,f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x))
  have hg : ∀ᵐ x : ℝ ∂volume,G x ∧ x≠1 := by
    have hn : ∀ᵐ x : ℝ ∂volume,x≠1 := by
      rw [ae_iff]
      simp only [not_not]
      convert (measure_singleton (μ := volume) (1 : ℝ)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
    filter_upwards [angular_smoothing_ae_tendsto hf hf1,hn] with x hx hn
    exact ⟨hx,hn⟩
  have hpos' : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc 0 1)≠0 := by
    have hh := hpos
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK] at hh
    simpa only [zero_add] using hh
  have hneg' : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' Kᶜ ∩ Ioc 0 1)≠0 := by
    have hh := hneg
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK.compl] at hh
    simpa only [zero_add] using hh
  obtain ⟨x,hx,hgx,hx1⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos' (ae_restrict_of_ae hg)
  obtain ⟨y,hy,hgy,hy1⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hneg' (ae_restrict_of_ae hg)
  have hxval : f x=1 := Set.indicator_of_mem (show (x : AddCircle (1 : ℝ))∈K from hx.1) _
  have hyval : f y=0 := Set.indicator_of_notMem (show (y : AddCircle (1 : ℝ))∉K from hy.1) _
  have hxi : x∈Ioo (0 : ℝ) 1 := ⟨hx.2.1,lt_of_le_of_ne hx.2.2 hx1⟩
  have hyi : y∈Ioo (0 : ℝ) 1 := ⟨hy.2.1,lt_of_le_of_ne hy.2.2 hy1⟩
  have hbound (a c : ℝ) (hac : a ≤ c) (hshort : c-a<1) (ha : G a) (hc : G c) :
      2*‖latticeVector m‖*|f a-f c| ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
    have ht := ((ha.sub hc).abs).const_mul (2*‖latticeVector m‖)
    apply le_of_tendsto ht
    have hrad : ∀ᶠ n : ℕ in atTop,(angularMollifier n).rOut<(1-(c-a))/2 :=
      (tendsto_order.mp angularMollifier_radius_tendsto).2 _ (by linarith)
    filter_upwards [hrad] with n hn
    apply circle_hat_calibration hm hK hP (angularMollifier n).contDiff_normed
      (angularMollifier n).integrable_normed (angularMollifier n).nonneg_normed
      (angularMollifier n).integral_normed (r := (angularMollifier n).rOut) ?_ hac (by linarith)
    rw [(angularMollifier n).tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [zero_sub,zero_add,Subset.refl]
  rcases le_total x y with hxy|hyx
  · have hh := hbound x y hxy (by linarith [hxi.1,hyi.2]) hgx hgy
    simpa only [hxval,hyval,sub_zero,abs_one,mul_one] using hh
  · have hh := hbound y x hyx (by linarith [hyi.1,hxi.2]) hgy hgx
    simpa only [hxval,hyval,zero_sub,abs_neg,abs_one,mul_one] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integer_lattice_norm_ge_one {m : Fin 3 → ℤ} (hm : m≠0) : 1≤‖latticeVector m‖ := by
  have hi : ∃ i,m i≠0 := by
    by_contra hn
    push Not at hn
    exact hm (funext hn)
  obtain ⟨i,hi⟩ := hi
  have hz : (1 : ℤ)≤|m i| := by
    have hh := abs_pos.mpr hi
    omega
  have hz' : (1 : ℝ)≤|(m i : ℝ)| := by exact_mod_cast hz
  have hh := PiLp.norm_apply_le (latticeVector m) i
  simp only [latticeVector,WithLp.ofLp_toLp,Real.norm_eq_abs] at hh
  exact hz'.trans hh

theorem Periodic.isMinimizerAt_connected_or_unit_integer_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧
        ‖latticeVector m‖=1 ∧ IsOpen K ∧ openRepresentative E=(integerCharacter m) ⁻¹' K ∧
        volume K=ENNReal.ofReal V) := by
  rcases Periodic.isMinimizerAt_connected_or_circle_phase hV hE hmin with hconn|
    ⟨m,K,hm,hK,he,hvol⟩
  · exact Or.inl hconn
  have hper : perimeter ((integerCharacter m) ⁻¹' K)=perimeter E := by
    rw [← he]
    exact perimeter_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)
  have hpos : volume K≠0 := by rw [hvol]; exact (ENNReal.ofReal_pos.mpr hV.1).ne'
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl hK.measurableSet (measure_ne_top _ _),hvol]
    have hv : ENNReal.ofReal V<(1 : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hV.2
    simpa only [measure_univ] using tsub_pos_iff_lt.mpr hv |>.ne'
  have hlo := circle_nontrivial_phase_lower_bound hm hK.measurableSet hpos hneg
    (hper ▸ hmin.1.2.ne)
  rw [hper] at hlo
  have hupper : perimeter E≤2 :=
    (hmin.2.2 (stripe V) (finitePerimeter_stripe ⟨hV.1.le,hV.2.le⟩)
      (volume_stripe ⟨hV.1.le,hV.2.le⟩)).trans (perimeter_stripe_le ⟨hV.1.le,hV.2.le⟩)
  have hup : (perimeter E).toReal≤2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)≠⊤) hupper
  have hnorm := integer_lattice_norm_ge_one hm
  have heq : (perimeter E).toReal=2 := by linarith
  have hper2 : perimeter E=2 := by
    rw [← ENNReal.ofReal_toReal hmin.1.2.ne,heq]
    norm_num
  exact Or.inr ⟨hper2,m,K,hm,by linarith,hK,he,hvol⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integer_lattice_norm_one_coordinate {m : Fin 3 → ℤ} (hn : ‖latticeVector m‖=1) :
    ∃ i : Fin 3,m=Pi.single i 1 ∨ m=Pi.single i (-1) := by
  classical
  have hm : m≠0 := by intro h; rw [h,latticeVector_zero,norm_zero] at hn; norm_num at hn
  have hi : ∃ i,m i≠0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  obtain ⟨i,hi⟩ := hi
  have hs : ∑ j : Fin 3,(m j : ℝ)^2=1 := by
    have hh := (EuclideanSpace.real_norm_sq_eq (latticeVector m)).symm
    rw [hn,one_pow] at hh
    simpa only [latticeVector,WithLp.ofLp_toLp] using hh
  have hmi : |(m i : ℝ)|=1 := by
    have hz : (1 : ℤ)≤|m i| := by have hh := abs_pos.mpr hi; omega
    have hz' : (1 : ℝ)≤|(m i : ℝ)| := by exact_mod_cast hz
    have hh := PiLp.norm_apply_le (latticeVector m) i
    rw [hn] at hh
    simp only [latticeVector,WithLp.ofLp_toLp,Real.norm_eq_abs] at hh
    exact le_antisymm hh hz'
  have hmisq : (m i : ℝ)^2=1 := by nlinarith [sq_abs (m i : ℝ)]
  have herase : ∑ j∈Finset.univ.erase i,(m j : ℝ)^2=0 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) (fun j ↦ (m j : ℝ)^2)
      (Finset.mem_univ i)
    linarith
  have hz (j : Fin 3) (hji : j≠i) : m j=0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (m j : ℝ))).mp herase
      j (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
    exact_mod_cast sq_eq_zero_iff.mp hh
  have hi' : m i=1 ∨ m i= -1 := by
    have hh : (m i : ℝ)=1 ∨ (m i : ℝ)= -1 := (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hmi
    exact_mod_cast hh
  refine ⟨i,?_⟩
  rcases hi' with hi'|hi'
  · left
    ext j
    by_cases hji : j=i
    · subst j; simpa only [Pi.single_eq_same] using hi'
    · rw [Pi.single_eq_of_ne hji,hz j hji]
  · right
    ext j
    by_cases hji : j=i
    · subst j; simpa only [Pi.single_eq_same] using hi'
    · rw [Pi.single_eq_of_ne hji,hz j hji]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePeriodize_abs_le_one {f : ℝ → ℝ} {a : ℝ}
    (hs : tsupport f ⊆ Ioo (a-1/2) (a+1/2))
    (hb : ∀ x,|f x|≤1) (x : ℝ) : |circlePeriodize f x|≤1 := by
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
    simp only [circlePeriodize,hn,tsum_zero,abs_zero,zero_le_one]

theorem circle_compact_calibration {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    {H : ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    {a : ℝ} (hs : tsupport H ⊆ Ioo (a-1/2) (a+1/2)) (hb : ∀ t,|H t|≤1) :
    ‖latticeVector m‖*|∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
      deriv H t| ≤ (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  let ψ := circlePeriodize H
  have hp : Function.Periodic ψ 1 := circlePeriodize_periodic H
  have hd (t : ℝ) (ht : t∈Icc (a-1/2) (a+1/2)) : deriv ψ t=deriv H t :=
    (circlePeriodize_eventuallyEq hHc hs ht).deriv_eq
  have hi : (∫ t in (a-1/2)..(a-1/2)+1,
      K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ))) =
      ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t := by
    rw [show a-1/2+1=a+1/2 by ring]
    calc
      _ = ∫ t in (a-1/2)..a+1/2,K.indicator (fun _ ↦ (1 : ℝ))
          (t : AddCircle (1 : ℝ))*deriv H t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t∈Icc (a-1/2) (a+1/2) := by
          simpa only [uIcc_of_le (show a-1/2≤a+1/2 by linarith)] using ht
        change K.indicator (real_periodic_deriv hp).lift (t : AddCircle (1 : ℝ)) =
          K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*deriv H t
        by_cases hk : (t : AddCircle (1 : ℝ))∈K
        · rw [Set.indicator_of_mem hk,Set.indicator_of_mem hk,one_mul]
          exact hd t ht'
        · rw [Set.indicator_of_notMem hk,Set.indicator_of_notMem hk,zero_mul]
      _ = _ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro t ht
        have hn : t∉tsupport H := fun hh ↦ ht ⟨(hs hh).1,(hs hh).2.le⟩
        rw [deriv_of_notMem_tsupport hn,mul_zero]
  have hh := integerCharacter_directional_variation hm hK hP
    (circlePeriodize_contDiff hH hHc) hp (circlePeriodize_abs_le_one hs hb) (a-1/2)
  rwa [hi] at hh

theorem circle_good_partition_variation {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hP : perimeter ((integerCharacter m) ⁻¹' K)≠⊤)
    (u : ℕ → ℝ) (hu : Monotone u) {a c : ℝ} (hus : ∀ i,u i∈Icc a c)
    (hshort : c-a<1) (n : ℕ)
    (hg : ∀ i,Tendsto (fun j ↦ ∫ t : ℝ,
      K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
        (angularMollifier j).normed volume (t-u i)) atTop
      (𝓝 (K.indicator (fun _ ↦ (1 : ℝ)) (u i : AddCircle (1 : ℝ))))) :
    ‖latticeVector m‖*(∑ i∈Finset.range n,
      |K.indicator (fun _ ↦ (1 : ℝ)) (u i : AddCircle (1 : ℝ))-
        K.indicator (fun _ ↦ (1 : ℝ)) (u (i+1) : AddCircle (1 : ℝ))|) ≤
      (perimeter ((integerCharacter m) ⁻¹' K)).toReal := by
  classical
  let f : ℝ → ℝ := fun t ↦ K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))
  have hf : Measurable f := (measurable_const.indicator hK).comp
    QuotientAddGroup.continuous_mk.measurable
  have hf1 (t : ℝ) : |f t|≤1 := by
    simp only [f,Set.indicator_apply]; split_ifs <;> norm_num
  let σ : ℕ → ℝ := fun i ↦ if 0≤f (u i)-f (u (i+1)) then 1 else -1
  have hσ (i : ℕ) : |σ i|≤1 := by dsimp [σ]; split_ifs <;> norm_num
  have he (i : ℕ) : σ i*(f (u i)-f (u (i+1)))=|f (u i)-f (u (i+1))| := by
    dsimp [σ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have ht := ((tendsto_finsetSum (Finset.range n) (fun i _ ↦
    ((hg i).sub (hg (i+1))).const_mul (σ i))).abs).const_mul ‖latticeVector m‖
  have hlim : ‖latticeVector m‖*|∑ i∈Finset.range n,σ i*(f (u i)-f (u (i+1)))| =
      ‖latticeVector m‖*∑ i∈Finset.range n,|f (u i)-f (u (i+1))| := by
    simp_rw [he]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _))]
  change Tendsto _ _ (𝓝 (‖latticeVector m‖*|∑ i∈Finset.range n,
    σ i*(f (u i)-f (u (i+1)))|)) at ht
  rw [hlim] at ht
  apply le_of_tendsto ht
  have hrad : ∀ᶠ j : ℕ in atTop,(angularMollifier j).rOut<(1-(c-a))/2 :=
    (tendsto_order.mp angularMollifier_radius_tendsto).2 _ (by linarith)
  filter_upwards [hrad] with j hj
  let b := (angularMollifier j).normed volume
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := (angularMollifier j).contDiff_normed
  let H := partitionSmoothTest b u σ n
  have hsub : tsupport H ⊆ Icc (a-(angularMollifier j).rOut) (c+(angularMollifier j).rOut) := by
    apply partitionSmoothTest_support hb.continuous _ hu hus
    rw [(angularMollifier j).tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [zero_sub,zero_add,Subset.refl]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H) hsub
  have hHs : tsupport H ⊆ Ioo ((a+c)/2-1/2) ((a+c)/2+1/2) := by
    intro t ht
    have hh := hsub ht
    constructor <;> linarith [hh.1,hh.2]
  have hh := circle_compact_calibration hm hK hP
    (partitionSmoothTest_contDiff hb u σ n) hHc hHs
    (partitionSmoothTest_bound hb.continuous
      (angularMollifier j).integrable_normed (angularMollifier j).nonneg_normed
      (angularMollifier j).integral_normed hu hσ n)
  rw [partitionSmoothTest_flux hf hf1 hb.continuous
    (angularMollifier j).integrable_normed] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circlePhaseGood_ae {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K) :
    ∀ᵐ x : ℝ ∂volume,circlePhaseGood K x := by
  apply angular_smoothing_ae_tendsto
    ((measurable_const.indicator hK).comp QuotientAddGroup.continuous_mk.measurable)
  intro t
  change |K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))|≤1
  classical
  by_cases ht : (t : AddCircle (1 : ℝ))∈K
  · rw [Set.indicator_of_mem ht]; norm_num
  · rw [Set.indicator_of_notMem ht]; norm_num

theorem circle_no_four_alternations {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2)
    {a b c d : ℝ} (hab : a≤b) (hbc : b ≤ c) (hcd : c≤d) (hshort : d-a<1)
    (ha : circlePhaseGood K a) (hb : circlePhaseGood K b)
    (hc : circlePhaseGood K c) (hd : circlePhaseGood K d)
    (ha0 : (a : AddCircle (1 : ℝ))∉K) (hb1 : (b : AddCircle (1 : ℝ))∈K)
    (hc0 : (c : AddCircle (1 : ℝ))∉K) (hd1 : (d : AddCircle (1 : ℝ))∈K) : False := by
  classical
  let u : ℕ → ℝ := fun i ↦ if i=0 then a else if i=1 then b else if i=2 then c else d
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases h0 : i=0
    · subst i; simpa [u] using hab
    by_cases h1 : i=1
    · subst i; simpa [u] using hbc
    by_cases h2 : i=2
    · subst i; simpa [u] using hcd
    simp only [u,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,
      ite_eq_right (by omega : i+1≠0),ite_eq_right (by omega : i+1≠1),
      ite_eq_right (by omega : i+1≠2),le_refl]
  have hus (i : ℕ) : u i∈Icc a d := by
    dsimp [u]
    split_ifs <;> constructor <;> linarith
  have hg (i : ℕ) : circlePhaseGood K (u i) := by
    dsimp [u]
    split_ifs <;> assumption
  have hh := circle_good_partition_variation hm hK (by rw [hP]; norm_num) u hu hus hshort 3 hg
  rw [hn,hP] at hh
  norm_num [Finset.sum_range_succ,u,Set.indicator_of_mem hb1,Set.indicator_of_mem hd1,
    Set.indicator_of_notMem ha0,Set.indicator_of_notMem hc0] at hh

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

theorem circle_equality_phase_interval {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hpos : volume K≠0) (hneg : volume Kᶜ≠0)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    ∃ z a b : ℝ,z≤a ∧ a<b ∧ b≤z+1 ∧
      (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1) : Set ℝ) =ᵐ[volume] Ioo a b ∧
      volume K=ENNReal.ofReal (b-a) := by
  classical
  have hzpos : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' Kᶜ ∩ Ioc 0 1)≠0 := by
    have hh := hneg
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK.compl] at hh
    simpa only [zero_add] using hh
  obtain ⟨z,hz,hgz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hzpos
    (ae_restrict_of_ae (circlePhaseGood_ae hK))
  have hz0 : (z : AddCircle (1 : ℝ))∉K := hz.1
  have hcpos : volume (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1))≠0 := by
    rwa [← AddCircle.add_projection_respects_measure (1 : ℝ) z hK]
  have hg : ∀ᵐ t : ℝ ∂volume,circlePhaseGood K t ∧ t≠z+1 :=
    (circlePhaseGood_ae hK).and (volume.ae_ne (z+1))
  obtain ⟨w,hw,hgw,hwne⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcpos (ae_restrict_of_ae hg)
  have hwi : w∈Ioo z (z+1) := ⟨hw.2.1,lt_of_le_of_ne hw.2.2 hwne⟩
  let S : Set ℝ := {t | t∈Ioo z (z+1) ∧ circlePhaseGood K t ∧ (t : AddCircle (1 : ℝ))∈K}
  have hSne : S.Nonempty := ⟨w,hwi,hgw,hw.1⟩
  have hlower : BddBelow S := ⟨z,fun _ ht ↦ ht.1.1.le⟩
  have hupper : BddAbove S := ⟨z+1,fun _ ht ↦ ht.1.2.le⟩
  let a := sInf S
  let b := sSup S
  have hza : z≤a := le_csInf hSne (fun _ ht ↦ ht.1.1.le)
  have hbz : b≤z+1 := csSup_le hSne (fun _ ht ↦ ht.1.2.le)
  have hab : a≤b := csInf_le_csSup hSne hlower hupper
  have hmid (x : ℝ) (hx : x∈Ioo a b) (hgx : circlePhaseGood K x) :
      (x : AddCircle (1 : ℝ))∈K := by
    obtain ⟨u,hu,hux⟩ := exists_lt_of_csInf_lt hSne hx.1
    obtain ⟨v,hv,hxv⟩ := exists_lt_of_lt_csSup hSne hx.2
    by_contra h0
    exact circle_no_four_alternations hm hK hn hP hu.1.1.le hux.le hxv.le
      (by linarith [hv.1.2]) hgz hu.2.1 hgx hv.2.1 hz0 hu.2.2 h0 hv.2.2
  have hae : (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1) : Set ℝ) =ᵐ[volume]
      Ioo a b := by
    filter_upwards [hg,volume.ae_ne a,volume.ae_ne b] with x hx hxa hxb
    apply propext
    constructor
    · intro h
      have hxS : x∈S := ⟨⟨h.2.1,lt_of_le_of_ne h.2.2 hx.2⟩,hx.1,h.1⟩
      exact ⟨lt_of_le_of_ne (csInf_le hlower hxS) (Ne.symm hxa),
        lt_of_le_of_ne (le_csSup hupper hxS) hxb⟩
    · intro h
      exact ⟨hmid x h hx.1,lt_of_le_of_lt hza h.1,h.2.le.trans hbz⟩
  have hvol : volume K=ENNReal.ofReal (b-a) := by
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) z hK,measure_congr hae,
      Real.volume_Ioo]
  have hab' : a<b := by
    by_contra hh
    have he : b=a := le_antisymm (le_of_not_gt hh) hab
    rw [hvol,he,sub_self,ENNReal.ofReal_zero] at hpos
    exact hpos rfl
  exact ⟨z,a,b,hza,hab',hbz,hae,hvol⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_coe_integer_zero (n : ℤ) : ((n : ℝ) : AddCircle (1 : ℝ))=0 := by
  have he : (n : ℝ)=n • (1 : ℝ) := by simp
  rw [he,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]

lemma circle_image_interval_eq_ball {a b : ℝ} (hab : a≤b) (hw : b-a≤1) :
    (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Ioo a b =
      Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2) := by
  rcases hab.eq_or_lt with rfl | _
  · simp
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    rw [Metric.mem_ball,dist_eq_norm,← AddCircle.coe_sub]
    have ht' : |t-(a+b)/2|<(b-a)/2 := abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by
      simpa only [abs_one] using (show |t-(a+b)/2|≤1/2 by linarith only [hw,ht']))]
    exact ht'
  · intro hx
    obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [Metric.mem_ball,dist_eq_norm,← AddCircle.coe_sub,AddCircle.norm_eq] at hx
    simp only [inv_one,one_mul,mul_one] at hx
    refine ⟨t-round (t-(a+b)/2),?_,?_⟩
    · have hh := abs_lt.mp hx
      constructor <;> linarith [hh.1,hh.2]
    · change ((t-(round (t-(a+b)/2) : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
      rw [AddCircle.coe_sub,circle_coe_integer_zero,sub_zero]

lemma circle_interval_ae_ball {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {z a b : ℝ} (hza : z≤a) (hab : a≤b) (hbz : b≤z+1)
    (hae : ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc z (z+1) : Set ℝ)
      =ᵐ[volume] Ioo a b) :
    K =ᵐ[volume] Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2) := by
  have he := circle_image_interval_eq_ball hab (show b-a≤1 by linarith)
  have hi (t : ℝ) (ht : t∈Ioc z (z+1)) :
      (t : AddCircle (1 : ℝ))∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2)
        ↔ t∈Ioo a b := by
    rw [← he]
    constructor
    · rintro ⟨u,hu,heq⟩
      have hui : u∈Ioc z (z+1) := ⟨lt_of_le_of_lt hza hu.1,hu.2.le.trans hbz⟩
      have hut : u=t := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hui ht).mp heq
      exact hut ▸ hu
    · intro ht'
      exact ⟨t,ht',rfl⟩
  have hp := AddCircle.measurePreserving_mk (1 : ℝ) z
  rw [← hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable ?_).mpr
  · apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hae] with t ht hti
    apply propext
    change ((t : AddCircle (1 : ℝ))∈K ↔ (t : AddCircle (1 : ℝ))∈Metric.ball _ _)
    rw [hi t hti]
    have hh := congrArg (fun p : Prop ↦ p) ht
    exact (and_iff_left hti).symm.trans
      (show ((t : AddCircle (1 : ℝ))∈K ∧ t∈Ioc z (z+1)) ↔ t∈Ioo a b from Iff.of_eq hh)
  · change MeasurableSet {x | (x∈K) = (x∈Metric.ball _ _)}
    have heq : {x : AddCircle (1 : ℝ) | (x∈K) =
        (x∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2))} =
        {x : AddCircle (1 : ℝ) | x∈K ↔
          x∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2)} := by
      ext x
      exact propext_iff
    rw [heq]
    exact hK.iff Metric.isOpen_ball.measurableSet

theorem circle_equality_phase_ball {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {V : ℝ} (hV : V∈Ioo 0 1) (hvol : volume K=ENNReal.ofReal V)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    ∃ c : AddCircle (1 : ℝ),K =ᵐ[volume] Metric.ball c (V/2) := by
  have hpos : volume K≠0 := by rw [hvol]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hV.1)
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl hK (measure_ne_top _ _),hvol]
    have hu : volume (univ : Set (AddCircle (1 : ℝ)))=1 := by simp
    rw [hu]
    exact ne_of_gt (tsub_pos_iff_lt.mpr ((ENNReal.ofReal_lt_one).mpr hV.2))
  obtain ⟨z,a,b,hza,hab,hbz,hae,hv⟩ := circle_equality_phase_interval hm hK hpos hneg hn hP
  have hw : b-a=V := by
    have hh := congrArg ENNReal.toReal (hv.symm.trans hvol)
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),ENNReal.toReal_ofReal hV.1.le] using hh
  refine ⟨(((a+b)/2 : ℝ) : AddCircle (1 : ℝ)),?_⟩
  rw [← hw]
  exact circle_interval_ae_ball hK hza hab.le hbz hae

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinate_ball_isometric_slab (V : ℝ) (i : Fin 3) (c : AddCircle (1 : ℝ)) :
    ∃ φ : Torus ≃ᵢ Torus,φ '' canonicalSlab V =
      (fun x : Torus ↦ x i) ⁻¹' Metric.ball c (V/2) := by
  classical
  let q : Torus := WithLp.toLp 2 (Pi.single i c)
  let φ := (torusCoordinatePermute (Equiv.swap (0 : Fin 3) i)).trans (IsometryEquiv.addRight q)
  have he (y : Torus) : (φ y) i=y 0+c := by
    change y (Equiv.swap (0 : Fin 3) i i)+q i=y 0+c
    simp [q]
  refine ⟨φ,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change dist ((φ y) i) c<V/2
    rw [he]
    change ‖y 0‖ < V/2 at hy
    simpa only [dist_eq_norm,add_sub_cancel_right] using hy
  · intro hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    change ‖(φ.symm x) 0‖<V/2
    have hg := he (φ.symm x)
    rw [φ.apply_symm_apply] at hg
    change dist (x i) c<V/2 at hx
    rw [hg] at hx
    simpa only [dist_eq_norm,add_sub_cancel_right] using hx

lemma integerCharacter_single (i : Fin 3) (n : ℤ) (x : Torus) :
    integerCharacter (Pi.single i n) x=n • x i := by
  classical
  simp [integerCharacter,Pi.single_apply]

theorem unit_character_equality_congruent_slab {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {V : ℝ} (hV : V∈Ioo 0 1) (hvol : volume K=ENNReal.ofReal V)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    CongruentAE ((integerCharacter m) ⁻¹' K) (canonicalSlab V) := by
  obtain ⟨c,hc⟩ := circle_equality_phase_ball hm hK hV hvol hn hP
  have hpre : (integerCharacter m) ⁻¹' K =ᵐ[torusVolume]
      (integerCharacter m) ⁻¹' Metric.ball c (V/2) :=
    (integerCharacter_measurePreserving hm).quasiMeasurePreserving.ae_eq_comp hc
  obtain ⟨i,hi⟩ := integer_lattice_norm_one_coordinate hn
  rcases hi with hi|hi
  · obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V i c
    refine ⟨φ,?_⟩
    rw [hφ]
    have he : (integerCharacter m) ⁻¹' Metric.ball c (V/2)=
        (fun x : Torus ↦ x i) ⁻¹' Metric.ball c (V/2) := by
      subst m
      ext x
      simp only [mem_preimage,integerCharacter_single,one_zsmul]
    exact hpre.trans (Eventually.of_forall (congrFun (congrArg (fun s : Set Torus ↦ (s : Torus → Prop)) he)))
  · obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V i (-c)
    refine ⟨φ,?_⟩
    rw [hφ]
    have he : (integerCharacter m) ⁻¹' Metric.ball c (V/2)=
        (fun x : Torus ↦ x i) ⁻¹' Metric.ball (-c) (V/2) := by
      subst m
      ext x
      simp only [mem_preimage,integerCharacter_single,neg_one_zsmul,Metric.mem_ball]
      rw [← dist_neg_neg (x i) (-c),neg_neg]
    exact hpre.trans (Eventually.of_forall (congrFun (congrArg (fun s : Set Torus ↦ (s : Torus → Prop)) he)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem Periodic.isMinimizerAt_connected_or_coordinate_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ CongruentAE E (canonicalSlab V)) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hrep : openRepresentative F=openRepresentative E := by
    unfold openRepresentative
    have hc : Fᶜ =ᵐ[torusVolume] Eᶜ := by
      filter_upwards [hae] with z hz
      exact congrArg Not hz
    exact congrArg (fun A : Set Torus ↦ Aᶜ) (volumeSupport_congr_ae hc)
  rcases Periodic.isMinimizerAt_connected_or_unit_integer_phase hV hF hmF with hc|
    ⟨hper,m,K,hm,hn,hK,he,hvol⟩
  · exact Or.inl (hrep ▸ hc)
  have hc : (integerCharacter m) ⁻¹' K =ᵐ[torusVolume] E := by
    rw [← he]
    exact (isMinimizerAt_openRepresentative_ae hV hF hmF).trans hae
  have hpE : perimeter E=2 := (perimeter_congr_ae hae).symm.trans hper
  have hpK : perimeter ((integerCharacter m) ⁻¹' K)=2 :=
    (perimeter_congr_ae hc).trans hpE
  obtain ⟨φ,hφ⟩ := unit_character_equality_congruent_slab hm hK.measurableSet hV hvol hn hpK
  refine Or.inr ⟨hpE,?_,φ,hc.symm.trans hφ⟩
  have hup := isMinimizerAt_perimeter_le_candidateProfile hV hmin
  rw [hpE] at hup
  have hvnon : 0≤ min V (1-V) := le_min hV.1.le (by linarith [hV.2])
  have hcand : 0 ≤ candidateProfile V := by
    unfold candidateProfile
    exact le_min (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))
      (le_min (by positivity) (by positivity))
  have h2 : (2 : ℝ) ≤ candidateProfile V := by
    simpa only [ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hcand] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
  have ht : candidateProfile V≤2*Real.sqrt (Real.pi*min V (1-V)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrt : 1≤Real.sqrt (Real.pi*min V (1-V)) := by linarith
  have hpiv : 1≤Real.pi*min V (1-V) := by
    have hs := Real.sq_sqrt (show 0≤Real.pi*min V (1-V) by positivity)
    nlinarith [Real.sqrt_nonneg (Real.pi*min V (1-V))]
  exact (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)

end CubicTorus

end
end

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

lemma isMinimizerAt_frontier_compl {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative Eᶜ)=frontier (openRepresentative E) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have haec : Fᶜ =ᵐ[torusVolume] Eᶜ := by
    filter_upwards [hae] with z hz
    exact congrArg Not hz
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  calc
    frontier (openRepresentative Eᶜ)=frontier (openRepresentative Fᶜ) :=
      congrArg frontier (openRepresentative_congr_ae haec).symm
    _=frontier (openRepresentative F) := by
      rw [isMinimizerAt_frontier_openRepresentative hV hF hmF,
        isMinimizerAt_frontier_openRepresentative hVc hF.compl
          ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmF),compl_compl,inter_comm]
    _=frontier (openRepresentative E) := congrArg frontier (openRepresentative_congr_ae hae)

theorem Periodic.isMinimizerAt_connected_or_standard_slab_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E) := by
  by_cases hc : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hc
  obtain ⟨hp,hr,hsl⟩ := (isMinimizerAt_connected_or_coordinate_slab hV hmin).resolve_left hc
  refine Or.inr ⟨hp,hr,?_⟩
  unfold StandardRegionAt
  split_ifs with hhalf
  · exact Or.inr (Or.inr ⟨hr.trans (min_le_left _ _),hsl⟩)
  · have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
    have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
    have hnc : ¬IsPreconnected (frontier (openRepresentative Eᶜ)) := by
      rwa [isMinimizerAt_frontier_compl hV hmin]
    obtain ⟨_,_,hslc⟩ := (isMinimizerAt_connected_or_coordinate_slab hVc hmc).resolve_left hnc
    exact Or.inr (Or.inr ⟨hr.trans (min_le_right _ _),hslc⟩)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab_oai := @OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab_oai
