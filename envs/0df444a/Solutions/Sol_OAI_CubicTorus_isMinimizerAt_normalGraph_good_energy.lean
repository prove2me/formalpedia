-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:53:22.946425+00:00
-- url     : https://prove2.me/submissions/5a2e0a98-545f-4426-8010-8a6a32378bb4

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_lower_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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

lemma perimeter_empty : perimeter ∅ = 0 := by
  simp [perimeter]

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

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

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

namespace CubicTorus

theorem smooth_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) : |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ f (x + t • a) a| ≤ ‖a‖ * (perimeter E).toReal := by
    have hp' : ∀ n x, f ((x + latticeVector n) + t • a) = f (x + t • a) := by
      intro n x
      rw [add_right_comm, hp]
    simpa only [Function.comp_def, id_eq, fderiv_comp_add_right] using
      abs_directional_flux_le hE (hf.comp (contDiff_id.add contDiff_const)) hp'
        (fun x => hb (x + t • a)) a
  calc
    _ = ‖∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a‖ := by
      simp_rw [hFTC, Real.norm_eq_abs]
    _ = ‖∫ t in Ioc (0 : ℝ) 1,
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a‖ := by
      rw [integral_integral_swap hi]
    _ ≤ (‖a‖ * (perimeter E).toReal) * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun t => (Real.norm_eq_abs _).trans_le (ht t)
    _ = _ := by simp [Measure.real]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  simpa only [mollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma smoothApprox_periodic {g : Cover → ℝ}
    (hp : ∀ n x, g (x + latticeVector n) = g x) (k : ℕ) (n : Fin 3 → ℤ) (x : Cover) :
    smoothApprox g k (x + latticeVector n) = smoothApprox g k x := by
  simp only [smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x + latticeVector n - y = (x - y) + latticeVector n by abel, hp]

lemma smoothApprox_ae_tendsto {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothApprox g n x) atTop (𝓝 (g x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_rOut_tendsto (K := 2) _ (locallyIntegrable_of_bounded hg hb)
  exact Eventually.of_forall fun n => by dsimp [mollifier]; ring_nf; rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem measurable_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  exact Eventually.of_forall fun n => smooth_test_translation_bound hE
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n) a

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

lemma setIntegral_lift_measurable {f : Torus → ℝ} (hf : Measurable f)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f z ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f (quotientMap x) := by
  change (∫ z in E, f z ∂Measure.map quotientMap (volume.restrict fundamentalCube)) = _
  rw [setIntegral_map hE hf.aestronglyMeasurable measurable_quotientMap.aemeasurable,
    Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma torus_test_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {g : Torus → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume|
      ≤ ‖a‖ * (perimeter E).toReal := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_translation_bound hP (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) a

lemma integral_difference_test {E : Set Torus} (hE : MeasurableSet E)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (a : Torus) :
    (∫ x in E, (g (x + a) - g x) ∂torusVolume) =
      ∫ x, (characteristic E (x - a) - characteristic E x) * g x ∂torusVolume := by
  have hi₁ : Integrable (fun x => characteristic E x * g (x + a)) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul
      (hg.comp (measurable_id.add_const a))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb (x + a))
  have hi₂ : Integrable (fun x => characteristic E x * g x) torusVolume := by
    apply Integrable.of_bound ((measurable_characteristic hE).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E x)).trans (hb x)
  have hi₃ : Integrable (fun x => characteristic E (x - a) * g x) torusVolume := by
    apply Integrable.of_bound (((measurable_characteristic hE).comp
      (measurable_id.sub_const a)).mul hg).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, Function.comp_def, id_eq]
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound E (x - a))).trans (hb x)
  have hs := (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding (fun x => characteristic E (x - a) * g x)
  simp only [add_sub_cancel_right] at hs
  calc
    _ = ∫ x, characteristic E x * (g (x + a) - g x) ∂torusVolume := by
      rw [← integral_indicator hE]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        classical
        by_cases hx : x ∈ E <;> simp [characteristic, hx]
    _ = (∫ x, characteristic E x * g (x + a) ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by
      simp_rw [mul_sub]
      exact integral_sub hi₁ hi₂
    _ = (∫ x, characteristic E (x - a) * g x ∂torusVolume) -
        ∫ x, characteristic E x * g x ∂torusVolume := by rw [hs]
    _ = _ := by simp_rw [sub_mul]; exact (integral_sub hi₃ hi₂).symm

theorem characteristic_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (a : Cover) :
    (∫ x, |characteristic E (x - quotientMap a) - characteristic E x| ∂torusVolume)
      ≤ ‖a‖ * (perimeter E).toReal := by
  let g : Torus → ℝ := fun x => characteristic E (x - quotientMap a) - characteristic E x
  have hg : Measurable g := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hb (x) : |g x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have heq (x) : g x * g x = |g x| := by
    rcases characteristic_dichotomy E (x - quotientMap a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
  have h := torus_test_translation_bound hE hP hg hb a
  rw [integral_difference_test hE hg hb] at h
  change |∫ x, g x * g x ∂torusVolume| ≤ _ at h
  simp_rw [heq] at h
  rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg (g x))] at h
  exact h

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma characteristic_translation_ae_of_perimeter_zero {E : Set Torus}
    (hE : MeasurableSet E) (hP : perimeter E = 0) (a : Torus) :
    (fun x ↦ characteristic E (x - a)) =ᵐ[torusVolume] characteristic E := by
  have h := characteristic_translation_bound hE (hP ▸ ENNReal.zero_ne_top) (representative a)
  rw [quotientMap_representative, hP, ENNReal.toReal_zero, mul_zero] at h
  have hg : Measurable (fun x ↦ |characteristic E (x - a) - characteristic E x|) :=
    (((measurable_characteristic hE).comp (measurable_id.sub_const a)).sub
      (measurable_characteristic hE)).abs
  have hi : Integrable (fun x ↦ |characteristic E (x - a) - characteristic E x|) torusVolume := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hi).1
    (le_antisymm h (integral_nonneg fun x ↦ abs_nonneg _))
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 (abs_eq_zero.1 hx)

theorem volume_eq_zero_or_one_of_perimeter_zero {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hP : perimeter E = 0) :
    torusVolume E = 0 ∨ torusVolume E = 1 := by
  wlog hEm : MeasurableSet E generalizing E
  · have hae := hE.toMeasurable_ae_eq
    have hP' : perimeter (toMeasurable torusVolume E) = 0 := (perimeter_congr_ae hae).trans hP
    have hh := this (measurableSet_toMeasurable torusVolume E).nullMeasurableSet hP'
      (measurableSet_toMeasurable torusVolume E)
    rwa [measure_congr hae] at hh
  have hall : ∀ᵐ a ∂torusVolume, ∀ᵐ x ∂torusVolume,
      characteristic E (x + a) = characteristic E x := by
    exact Eventually.of_forall fun a ↦ by
      have hh := characteristic_translation_ae_of_perimeter_zero hEm hP (-a)
      filter_upwards [hh] with x hx
      simpa only [sub_neg_eq_add] using hx
  have hswap := (Measure.ae_ae_comm (μ := torusVolume) (ν := torusVolume)
    (p := fun a x ↦ characteristic E (x + a) = characteristic E x)
    (measurableSet_eq_fun ((measurable_characteristic hEm).comp (measurable_snd.add measurable_fst))
      ((measurable_characteristic hEm).comp measurable_snd))).1 hall
  obtain ⟨x, hx⟩ := hswap.exists
  have hav := integral_congr_ae hx
  rw [integral_add_left_eq_self, integral_characteristic hE, integral_const] at hav
  simp only [Measure.real_def, torusVolume_univ, ENNReal.toReal_one, one_smul] at hav
  rcases characteristic_dichotomy E x with h0 | h1
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).1 (hav.trans h0)).resolve_right (measure_ne_top _ _)
  · right
    have hh := congrArg ENNReal.ofReal (hav.trans h1)
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] using hh

theorem perimeter_pos_of_volume {V : ℝ} (hV : V ∈ Ioo 0 1) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hvolume : torusVolume E = ENNReal.ofReal V) :
    0 < perimeter E := by
  apply bot_lt_iff_ne_bot.2
  intro hzero
  rcases volume_eq_zero_or_one_of_perimeter_zero hE hzero with h0 | h1
  · rw [hvolume] at h0
    exact (ENNReal.ofReal_pos.2 hV.1).ne' h0
  · rw [hvolume] at h1
    have hh := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_ofReal hV.1.le, ENNReal.toReal_one] at hh
    exact hV.2.ne hh

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
open Filter
open scoped Topology Convolution RealInnerProductSpace

lemma characteristic_nonneg (E : Set Torus) (x : Torus) : 0 ≤ characteristic E x := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma gradient_const_sub (f : Cover → ℝ) (c : ℝ) (x : Cover) :
    gradient (fun y ↦ c - f y) x = -gradient f x := by
  simp only [gradient, fderiv_const_sub, map_neg]

end CubicTorus

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

theorem coordinate_variation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    FinitePerimeter (coordinateRegion i f t E) ∧
    torusVolume.real (coordinateRegion i f t E) = torusVolume.real E +
      t * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f x (EuclideanSpace.single i 1) ∧
    (perimeter (coordinateRegion i f t E)).toReal ≤
      (1 + 2 * |t| * M) * (perimeter E).toReal := by
  refine ⟨finitePerimeter_coordinateRegion i hf hp hM hface ht hE hP,
    volume_coordinateRegion i hf hp hM hface ht hE, ?_⟩
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)
    (perimeter_coordinateRegion_le i hf hp hM hface ht hE hP)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

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

lemma directionalFlux_add (E : Set Torus) (i : Fin 3) {f g : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    directionalFlux E i (fun x ↦ f x + g x) = directionalFlux E i f + directionalFlux E i g := by
  unfold directionalFlux
  change (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    fderiv ℝ (f + g) x (EuclideanSpace.single i 1)) = _
  simp only [fderiv_add (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt, add_apply]
  exact integral_add ((integrableOn_directionalDeriv i hf).mono_set inter_subset_left)
    ((integrableOn_directionalDeriv i hg).mono_set inter_subset_left)

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

lemma exists_positive_directionalFlux {E : Set Torus} (hP : 0 < perimeter E) :
    ∃ (i : Fin 3) (f : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ n x, f (x + latticeVector n) = f x) ∧ 0 < directionalFlux E i f := by
  have hh : ∃ F, AdmissibleField F ∧
      0 < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    by_contra! hn
    have : perimeter E ≤ 0 := iSup_le fun F ↦ iSup_le fun hF ↦ by
      exact (ENNReal.ofReal_eq_zero.2 (hn F hF)).le
    exact not_le_of_gt hP this
  obtain ⟨F, hF, hp⟩ := hh
  rw [flux_sum_components E hF.1] at hp
  have hi : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ F x i) := by
    by_contra! hn
    exact not_le_of_gt hp (Finset.sum_nonpos fun i _ ↦ hn i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, fun x ↦ F x i, (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF.1, ?_, hi⟩
  intro n x
  dsimp only
  rw [hF.2.1]

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

lemma wallCutoff_halfShift (i : Fin 3) (x : Cover) :
    wallCutoff i (x + (1 / 2 : ℝ) • EuclideanSpace.single i 1) = 1 - wallCutoff i x := by
  have he : 2 * Real.pi * (x + (1 / 2 : ℝ) • (EuclideanSpace.single i 1 : Cover)) i =
      2 * Real.pi * x i + Real.pi := by
    simp
    ring
  rw [wallCutoff, he, Real.cos_add_pi]
  unfold wallCutoff
  ring

lemma smooth_flux_translation {F : Cover → Cover}
    (hc : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  rw [← setIntegral_lift (continuous_divergence hc) (divergence_periodic hp) hpre]
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F (y - a)) :=
    hc.comp (contDiff_id.sub contDiff_const)
  have hGp : ∀ n x, F ((x + latticeVector n) - a) = F (x - a) := by
    intro n x
    rw [add_sub_right_comm, hp]
  rw [← setIntegral_lift (continuous_divergence hGc) (divergence_periodic hGp) hE]
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
    rw [hn, divergence_periodic hp]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

lemma directionalFlux_translation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f (x + a)) =
      directionalFlux E i f := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f (x + a) • (EuclideanSpace.single i 1 : Cover)) :=
    (hf.comp (contDiff_id.add contDiff_const)).smul contDiff_const
  have hFp : ∀ n x, f ((x + latticeVector n) + a) • (EuclideanSpace.single i 1 : Cover) =
      f (x + a) • EuclideanSpace.single i 1 := by
    intro n x
    rw [add_right_comm, hp]
  have hh := smooth_flux_translation hFc hFp a hE
  simp only [sub_add_cancel] at hh
  simp_rw [divergence_smul_const (hf.differentiable (by simp)).differentiableAt] at hh
  unfold directionalFlux
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (divergence_smul_const
    ((hf.comp (contDiff_id.add contDiff_const)).differentiable (by simp)).differentiableAt
    (EuclideanSpace.single i 1)).symm

theorem exists_positive_wallVariation {E : Set Torus} (hE : MeasurableSet E)
    (hP : 0 < perimeter E) :
    ∃ (a : Cover) (D : WallVariation),
      0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) D.coordinate D.function := by
  obtain ⟨i, f, hf, hp, hflux⟩ := exists_positive_directionalFlux hP
  let f₀ : Cover → ℝ := fun x ↦ wallCutoff i x * f x
  let f₁ : Cover → ℝ := fun x ↦ (1 - wallCutoff i x) * f x
  have hc₀ : ContDiff ℝ (⊤ : ℕ∞) f₀ := (wallCutoff_contDiff i).mul hf
  have hc₁ : ContDiff ℝ (⊤ : ℕ∞) f₁ := (contDiff_const.sub (wallCutoff_contDiff i)).mul hf
  have hp₀ : ∀ n x, f₀ (x + latticeVector n) = f₀ x := by
    intro n x
    dsimp only [f₀]
    rw [wallCutoff_periodic, hp]
  have hp₁ : ∀ n x, f₁ (x + latticeVector n) = f₁ x := by
    intro n x
    dsimp only [f₁]
    rw [wallCutoff_periodic, hp]
  have he : (fun x ↦ f₀ x + f₁ x) = f := by
    funext x
    dsimp only [f₀, f₁]
    ring
  have hs : 0 < directionalFlux E i f₀ + directionalFlux E i f₁ := by
    rw [← directionalFlux_add E i hc₀ hc₁, he]
    exact hflux
  by_cases hpos : 0 < directionalFlux E i f₀
  · have hface₀ : ∀ x, x i = 0 ∨ x i = 1 → f₀ x = 0 := by
      intro x hx
      simp [f₀, wallCutoff_face i x hx]
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hc₀ hp₀ hface₀
    refine ⟨0, D, ?_⟩
    have hz : quotientMap 0 = 0 := by ext j; simp [quotientMap]
    simpa only [hi, hfD, hz, add_zero, preimage_id'] using hpos
  · have hpos₁ : 0 < directionalFlux E i f₁ := by linarith
    let a : Cover := (1 / 2 : ℝ) • EuclideanSpace.single i 1
    let g : Cover → ℝ := fun x ↦ f₁ (x + a)
    have hgc : ContDiff ℝ (⊤ : ℕ∞) g := hc₁.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp only [g]
      rw [add_right_comm, hp₁]
    have hgf : ∀ x, x i = 0 ∨ x i = 1 → g x = 0 := by
      intro x hx
      dsimp only [g, f₁, a]
      rw [wallCutoff_halfShift, wallCutoff_face i x hx]
      ring
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hgc hgp hgf
    refine ⟨a, D, ?_⟩
    rw [hi, hfD]
    change 0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f₁ (x + a))
    rwa [directionalFlux_translation i hc₁ hp₁ a hE]

end CubicTorus

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

namespace CubicTorus

lemma measurableSet_coordinateBox (r : ℝ) : MeasurableSet (coordinateBox r) := by
  simp only [coordinateBox, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_lt (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))) measurable_const

lemma coordinateBox_lift_preimage {r : ℝ} (hr : r ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' coordinateBox r) =
      univ.pi (fun _ : Fin 3 ↦ Ico 0 r) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    (∀ i, ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) < r)) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc i)
    exact ⟨(hc i).1, he ▸ hs i⟩
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := fun i ↦
      ⟨(hx i (mem_univ i)).1, (hx i (mem_univ i)).2.trans_le hr.2⟩
    refine ⟨hc, fun i ↦ ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc i)]
    exact (hx i (mem_univ i)).2

lemma volume_coordinateBox {r : ℝ} (hr : r ∈ Icc 0 1) :
    torusVolume (coordinateBox r) = ENNReal.ofReal (r ^ 3) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_coordinateBox r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_coordinateBox r)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter
      (measurable_quotientMap (measurableSet_coordinateBox r))).nullMeasurableSet)
  rw [coordinateBox_lift_preimage hr] at hm
  rw [← hm, Real.volume_pi_Ico]
  simp [← ENNReal.ofReal_pow hr.1, Finset.prod_const]

end CubicTorus

namespace CubicTorus
open Filter

lemma representative_norm_le_box {r : ℝ} (hr : 0 ≤ r) {x : Torus}
    (hx : x ∈ coordinateBox r) : ‖representative x‖ ≤ 3 * r := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have hb (i : Fin 3) : ‖(representative x).ofLp i‖ ^ 2 ≤ r ^ 2 := by
    have h0 := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).2.1
    have h1 := hx i
    change ‖((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ)‖ ^ 2 ≤ r ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hb i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    _ ≤ 3 * r ^ 2 := by exact_mod_cast hs
    _ ≤ (3 * r) ^ 2 := by nlinarith [sq_nonneg r]

theorem bv_cubical_isoperimetric {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {r : ℝ} (hr : r ∈ Icc 0 1) :
    (torusVolume E).toReal * (r ^ 3 - (torusVolume E).toReal) ≤
      3 * r ^ 4 * (perimeter E).toReal := by
  let B := coordinateBox r
  let ν := torusVolume.restrict B
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hB : MeasurableSet B := measurableSet_coordinateBox r
  have hvol : ν.real univ = r ^ 3 := by
    simp only [ν, Measure.real, Measure.restrict_apply_univ, B, volume_coordinateBox hr,
      ENNReal.toReal_ofReal (pow_nonneg hr.1 3)]
  let g : Torus × Torus → ℝ := fun z ↦
    characteristic E z.1 * (1 - characteristic E (z.1 + z.2))
  have hgm : Measurable g := (measurable_characteristic hE |>.comp measurable_fst).mul
    (measurable_const.sub (measurable_characteristic hE |>.comp (measurable_fst.add measurable_snd)))
  have hgb (z : Torus × Torus) : |g z| ≤ 1 := by
    rcases characteristic_dichotomy E z.1 with h | h <;>
      rcases characteristic_dichotomy E (z.1 + z.2) with h' | h' <;> simp [g, h, h']
  have hgi : Integrable g (torusVolume.prod ν) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hchi (x : Torus) : Integrable (fun a ↦ characteristic E (x + a)) torusVolume :=
    Integrable.of_bound ((measurable_characteristic hE).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable 1
        (Eventually.of_forall fun a ↦ characteristic_bound E (x + a))
  have hchiB (x : Torus) : (∫ a, characteristic E (x + a) ∂ν) ≤ V := by
    calc
      _ ≤ ∫ a, characteristic E (x + a) ∂torusVolume :=
        setIntegral_le_integral (hchi x) (Eventually.of_forall fun a ↦ characteristic_nonneg E _)
      _ = V := by rw [integral_add_left_eq_self, integral_characteristic hE.nullMeasurableSet]
  have hinner (x : Torus) : characteristic E x * (r ^ 3 - V) ≤ ∫ a, g (x, a) ∂ν := by
    change _ ≤ ∫ a, characteristic E x * (1 - characteristic E (x + a)) ∂ν
    rw [integral_const_mul, integral_sub (integrable_const _) (hchi x).integrableOn,
      integral_const, smul_eq_mul, mul_one, hvol]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hchiB x) _) (characteristic_nonneg E x)
  have hlow : V * (r ^ 3 - V) ≤ ∫ x, ∫ a, g (x, a) ∂ν ∂torusVolume := by
    calc
      _ = ∫ x, characteristic E x * (r ^ 3 - V) ∂torusVolume := by
        rw [integral_mul_const, integral_characteristic hE.nullMeasurableSet]
      _ ≤ _ := integral_mono ((integrable_characteristic hE).mul_const _) hgi.integral_prod_left hinner
  have hupper (a : Torus) : (∫ x, g (x, a) ∂torusVolume) ≤ ‖representative a‖ * P := by
    have hi : Integrable (fun x ↦ |characteristic E (x + a) - characteristic E x|) torusVolume := by
      apply Integrable.of_bound
        (((measurable_characteristic hE).comp (measurable_id.add_const a)).sub
          (measurable_characteristic hE)).abs.aestronglyMeasurable 1
      exact Eventually.of_forall fun x ↦ by
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
    calc
      _ ≤ ∫ x, |characteristic E (x + a) - characteristic E x| ∂torusVolume := by
        apply integral_mono (Integrable.of_bound
          (hgm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
            (Eventually.of_forall fun x ↦ hgb (x, a))) hi
        intro x
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
      _ ≤ _ := by simpa only [quotientMap_neg, quotientMap_representative, sub_neg_eq_add, norm_neg] using
        characteristic_translation_bound hE hP (-representative a)
  have hup : (∫ a, ∫ x, g (x, a) ∂torusVolume ∂ν) ≤ 3 * r ^ 4 * P := by
    calc
      _ ≤ ∫ a, (3 * r * P) ∂ν := by
        apply integral_mono_ae hgi.integral_prod_right (integrable_const _)
        filter_upwards [ae_restrict_mem hB] with a ha
        exact (hupper a).trans (mul_le_mul_of_nonneg_right
          (representative_norm_le_box hr.1 ha) ENNReal.toReal_nonneg)
      _ = _ := by rw [integral_const, smul_eq_mul, hvol]; ring
  exact hlow.trans ((integral_integral_swap hgi).le.trans hup)

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

theorem bv_isoperimetric_small_of_measurable {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  by_cases hz : V = 0
  · change V ^ (2 / 3 : ℝ) ≤ 12 * P
    rw [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity
  have hVp : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hz)
  let r := (2 * V) ^ (1 / 3 : ℝ)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hr3 : r ^ 3 = 2 * V := by
    dsimp only [r]
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2 * V)
      (by norm_num : (3 : ℕ) ≠ 0)
  have hr1 : r ≤ 1 := by
    have hh : 2 * V ≤ 1 := by dsimp only [V]; linarith
    dsimp only [r]
    exact (Real.rpow_le_rpow (by positivity) hh (by norm_num)).trans_eq (Real.one_rpow _)
  have hi := bv_cubical_isoperimetric hE hP ⟨hr0.le, hr1⟩
  change V * (r ^ 3 - V) ≤ 3 * r ^ 4 * P at hi
  rw [hr3] at hi
  have hi' : V ^ 2 ≤ 3 * r ^ 4 * P := by nlinarith [hi]
  have hs : r ^ 4 * (r ^ 2 - 12 * P) ≤ 0 := by
    have hsq := congrArg (fun a : ℝ ↦ a ^ 2) hr3
    nlinarith [hsq]
  have hr2 : r ^ 2 ≤ 12 * P := by
    have hh := nonpos_of_mul_nonpos_right hs (pow_pos hr0 4)
    linarith
  have he : (2 * V) ^ (2 / 3 : ℝ) = r ^ 2 := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * V)]
    congr 1
    norm_num
  change V ^ (2 / 3 : ℝ) ≤ 12 * P
  calc
    _ ≤ (2 * V) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hV0 (by linarith) (by norm_num)
    _ = r ^ 2 := he
    _ ≤ _ := hr2

theorem bv_isoperimetric_small {E : Set Torus} (hE : FinitePerimeter E)
    (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  have he := hE.1.toMeasurable_ae_eq
  have hp := perimeter_congr_ae he
  have hv : torusVolume (toMeasurable torusVolume E) = torusVolume E :=
    measure_congr he
  have hh := bv_isoperimetric_small_of_measurable
    (measurableSet_toMeasurable torusVolume E) (hp ▸ hE.2.ne) (by simpa only [hv] using hV)
  simpa only [hp, hv] using hh

end CubicTorus

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

theorem normalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ z, w z.1 ∂(μ : Measure NormalBundle)) := by
  let W : C(NormalBundle, ℝ) := ⟨fun z ↦ w z.1,
    hw.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hiW : Integrable W (μ : Measure NormalBundle) :=
    W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : weightedPerimeter E w ≤ ENNReal.ofReal (∫ z, W z ∂(μ : Measure NormalBundle)) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    rw [← normalMeasure_weighted_flux hμ hw hp hF]
    apply integral_mono ((W.continuous.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hiW
    intro z
    exact (mul_le_mul_of_nonneg_left (normalTest_le_one hF z) (hn z.1)).trans_eq (mul_one _)
  have htop : weightedPerimeter E w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply normalMeasure_weighted_saturation hμ W
  intro F hF
  change (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ _
  rw [normalMeasure_weighted_flux hμ hw hp hF]
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
  exact le_iSup_of_le F (le_iSup_of_le hF le_rfl)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma exists_admissible_flux_gt (E : Set Torus) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Cover → Cover) (_hF : AdmissibleField F),
      (perimeter E).toReal - ε < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  by_cases h : (perimeter E).toReal < ε
  · refine ⟨fun _ ↦ 0, admissible_zero, ?_⟩
    simpa only [divergence_zero, integral_zero] using sub_neg.mpr h
  · have hn : 0 ≤ (perimeter E).toReal - ε := sub_nonneg.mpr (le_of_not_gt h)
    by_contra! hnone
    have hb : perimeter E ≤ ENNReal.ofReal ((perimeter E).toReal - ε) := by
      exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hnone F hF)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hn] at hh
    linarith

end CubicTorus

namespace CubicTorus

lemma regionDistance_nonneg (E F : Set Torus) : 0 ≤ regionDistance E F :=
  integral_nonneg (fun _ ↦ norm_nonneg _)

lemma abs_realVolume_sub_le_regionDistance {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |torusVolume.real E - torusVolume.real F| ≤ regionDistance E F := by
  rw [Measure.real_def, Measure.real_def, ← integral_characteristic hE.nullMeasurableSet,
    ← integral_characteristic hF.nullMeasurableSet,
    ← integral_sub (integrable_characteristic hE) (integrable_characteristic hF)]
  exact norm_integral_le_integral_norm (fun x : Torus ↦ characteristic E x - characteristic F x)

lemma regionDistance_translation (E F : Set Torus) (a : Torus) :
    regionDistance ((fun z ↦ z + a) ⁻¹' E) ((fun z ↦ z + a) ⁻¹' F) = regionDistance E F := by
  have he (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' E) x = characteristic E (x + a) := by
    by_cases hx : x + a ∈ E <;> simp [characteristic, hx]
  have hf (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' F) x = characteristic F (x + a) := by
    by_cases hx : x + a ∈ F <;> simp [characteristic, hx]
  unfold regionDistance
  simp_rw [he, hf]
  exact (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding
      (fun x : Torus ↦ ‖characteristic E x - characteristic F x‖)

lemma characteristic_mul_eq_indicator (E : Set Torus) (g : Torus → ℝ) :
    (fun x ↦ characteristic E x * g x) = E.indicator g := by
  funext x
  by_cases hx : x ∈ E <;> simp [characteristic, hx]

lemma abs_weighted_characteristic_sub_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {g : Torus → ℝ}
    (hg : Measurable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M) :
    |(∫ x, characteristic E x * g x ∂torusVolume) -
      (∫ x, characteristic F x * g x ∂torusVolume)| ≤ M * regionDistance E F := by
  have hi : Integrable g torusVolume := Integrable.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall hb)
  have hiE : Integrable (fun x ↦ characteristic E x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hE
  have hiF : Integrable (fun x ↦ characteristic F x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hF
  rw [← integral_sub hiE hiF]
  calc
    _ ≤ ∫ x, ‖characteristic E x * g x - characteristic F x * g x‖ ∂torusVolume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖characteristic E x - characteristic F x‖ ∂torusVolume := by
      apply integral_mono (hiE.sub hiF).norm
        (((integrable_characteristic hE).sub (integrable_characteristic hF)).norm.const_mul M)
      intro x
      change ‖characteristic E x * g x - characteristic F x * g x‖ ≤
        M * ‖characteristic E x - characteristic F x‖
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

lemma directionalFlux_eq_pairing (E : Set Torus) (hE : MeasurableSet E)
    (D : WallVariation) :
    directionalFlux E D.coordinate D.function =
      ∫ x, characteristic E x *
        fderiv ℝ D.function (representative x) (EuclideanSpace.single D.coordinate 1) ∂torusVolume := by
  rw [characteristic_mul_eq_indicator, integral_indicator hE]
  exact (setIntegral_lift
    ((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    (fun n x ↦ by rw [fderiv_periodic D.periodic]) hE).symm

lemma WallVariation.directionalDeriv_bound (D : WallVariation) (x : Cover) :
    ‖fderiv ℝ D.function x (EuclideanSpace.single D.coordinate 1)‖ ≤ (D.bound : ℝ) := by
  have hM : ‖fderiv ℝ D.function x‖ ≤ (D.bound : ℝ) := by exact_mod_cast D.derivative_bound x
  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ D.function x)
    (EuclideanSpace.single D.coordinate 1)).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

lemma WallVariation.flux_lipschitz (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |directionalFlux E D.coordinate D.function - directionalFlux F D.coordinate D.function| ≤
      (D.bound : ℝ) * regionDistance E F := by
  rw [directionalFlux_eq_pairing E hE, directionalFlux_eq_pairing F hF]
  apply abs_weighted_characteristic_sub_le hE hF
    (((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp
      measurable_representative)
  intro x
  exact D.directionalDeriv_bound _

end CubicTorus

namespace CubicTorus

lemma positive_flux_nearby (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hδ : 0 < directionalFlux E D.coordinate D.function)
    (hd : regionDistance E F < directionalFlux E D.coordinate D.function /
      (4 * ((D.bound : ℝ) + 1))) :
    directionalFlux E D.coordinate D.function / 2 <
      directionalFlux F D.coordinate D.function := by
  have hh := (le_abs_self _).trans (D.flux_lipschitz hE hF)
  have hd' := (lt_div_iff₀ (by positivity : 0 < 4 * ((D.bound : ℝ) + 1))).1 hd
  have hnon := regionDistance_nonneg E F
  have hM := D.bound.coe_nonneg
  nlinarith

theorem local_comparison_of_positive_flux {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) (D : WallVariation)
    (hδ : 0 < directionalFlux E D.coordinate D.function) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      MeasurableSet F → perimeter F ≠ ⊤ → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let δ := directionalFlux E D.coordinate D.function
  let M : ℝ := D.bound
  let p := (perimeter E).toReal
  refine ⟨δ / (4 * (M + 1)), 4 * M * p / δ, by positivity, by positivity, ?_⟩
  intro F hF hFP hd
  have hδF := positive_flux_nearby D hE hF hδ hd
  let δF := directionalFlux F D.coordinate D.function
  let d := regionDistance E F
  have hd0 : 0 ≤ d := regionDistance_nonneg _ _
  have hM : 0 ≤ M := D.bound.coe_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := hδ
  have hf0 : 0 < δF := by dsimp only [δF]; linarith
  have hδF' : δ / 2 < δF := hδF
  let t := (torusVolume.real E - torusVolume.real F) / δF
  have ht_abs : |t| ≤ d / δF := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hf0]
    exact div_le_div_of_nonneg_right (abs_realVolume_sub_le_regionDistance hE hF) hf0.le
  have ht2 : |t| ≤ 2 * d / δ := by
    apply ht_abs.trans
    apply (div_le_div_iff₀ hf0 hδ0).2
    nlinarith
  have hd' : d * (4 * (M + 1)) < δ :=
    (lt_div_iff₀ (by positivity : 0 < 4 * (M + 1))).1 hd
  have htM : |t| * M < 1 := by
    have hh := mul_le_mul_of_nonneg_right ht2 hM
    have hh' : (2 * d / δ) * M < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hδ0]
      nlinarith
    exact hh.trans_lt hh'
  obtain ⟨hG, hGv, hGP⟩ := coordinate_variation D.coordinate D.smooth D.periodic
    D.derivative_bound D.faces htM hF hFP
  have hvol : torusVolume (coordinateRegion D.coordinate D.function t F) = torusVolume E := by
    have hv : torusVolume.real (coordinateRegion D.coordinate D.function t F) =
        torusVolume.real E := by
      rw [hGv]
      change torusVolume.real F + t * δF = torusVolume.real E
      dsimp only [t]
      field_simp
      ring
    have hh := congrArg ENNReal.ofReal hv
    simpa only [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hminimal : p ≤ (1 + 2 * |t| * M) * (perimeter F).toReal := by
    apply (ENNReal.toReal_mono hG.2.ne (hmin.2.2 _ hG (hvol.trans hmin.2.1))).trans hGP
  by_cases hl : p ≤ (perimeter F).toReal
  · exact hl.trans (le_add_of_nonneg_right (by positivity))
  · have hl' : (perimeter F).toReal ≤ p := le_of_not_ge hl
    have hscale : 2 * |t| * M ≤ (4 * M / δ) * d := by
      have hh := mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ 2 * M)
      calc
        2 * |t| * M = |t| * (2 * M) := by ring
        _ ≤ (2 * d / δ) * (2 * M) := hh
        _ = (4 * M / δ) * d := by ring
    have h1 := mul_le_mul_of_nonneg_right hscale (ENNReal.toReal_nonneg (a := perimeter F))
    have h2 := mul_le_mul_of_nonneg_left hl' (by positivity : 0 ≤ (4 * M / δ) * d)
    have heq : ((4 * M / δ) * d) * p = (4 * M * p / δ) * d := by ring
    nlinarith

end CubicTorus

namespace CubicTorus

lemma regionDistance_congr_ae {E E' F F' : Set Torus}
    (hE : E =ᵐ[torusVolume] E') (hF : F =ᵐ[torusVolume] F') :
    regionDistance E F = regionDistance E' F' := by
  apply integral_congr_ae
  filter_upwards [hE, hF] with x hx hy
  have hx' : x ∈ E ↔ x ∈ E' := Iff.of_eq hx
  have hy' : x ∈ F ↔ x ∈ F' := Iff.of_eq hy
  by_cases ha : x ∈ E <;> by_cases hb : x ∈ F <;> simp_all [characteristic]

theorem isMinimizerAt_local_quasiminimal {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      FinitePerimeter F → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let E₀ := toMeasurable torusVolume E
  have hE₀ : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have he : E₀ =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hm₀ : IsMinimizerAt V E₀ := (isMinimizerAt_congr_ae he).2 hmin
  obtain ⟨a, D, hδ⟩ := exists_positive_wallVariation hE₀
    (perimeter_pos_of_volume hV hm₀.1.1 hm₀.2.1)
  let R : Torus → Torus := fun z ↦ z + quotientMap a
  have hRm : Measurable R := (continuous_add_const _).measurable
  obtain ⟨ε, C, heps, hC, hcompare⟩ := local_comparison_of_positive_flux
    (isMinimizerAt_translation hm₀ (quotientMap a)) (hE₀.preimage hRm) D hδ
  refine ⟨ε, C, heps, hC, ?_⟩
  intro F hF hd
  let F₀ := toMeasurable torusVolume F
  have hF₀ : MeasurableSet F₀ := measurableSet_toMeasurable _ _
  have hf : F₀ =ᵐ[torusVolume] F := hF.1.toMeasurable_ae_eq
  have hfp : FinitePerimeter F₀ := (finitePerimeter_congr_ae hf).2 hF
  have hdist : regionDistance (R ⁻¹' E₀) (R ⁻¹' F₀) = regionDistance E F := by
    rw [regionDistance_translation, regionDistance_congr_ae he hf]
  have hh := hcompare (R ⁻¹' F₀) (hF₀.preimage hRm)
    (finitePerimeter_translation hfp (quotientMap a)).2.ne (hdist ▸ hd)
  rw [hdist, perimeter_translation hm₀.1.1, perimeter_translation hfp.1,
    perimeter_congr_ae he, perimeter_congr_ae hf] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma divergence_add_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y + G y) point = divergence F point + divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F + G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_add hF hG]
  simp [divergence, Finset.sum_add_distrib]

lemma admissible_convex_cutoff {w : Cover → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    AdmissibleField (fun x ↦ w x • F x + (1 - w x) • G x) := by
  refine ⟨(hw.smul hF.1).add ((contDiff_const.sub hw).smul hG.1), ?_, ?_⟩
  · intro n x
    dsimp only
    rw [hp, hF.2.1, hG.2.1]
  · intro x
    calc
      _ ≤ ‖w x • F x‖ + ‖(1 - w x) • G x‖ := norm_add_le _ _
      _ = w x * ‖F x‖ + (1 - w x) * ‖G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hb x).1, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      _ ≤ w x * 1 + (1 - w x) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hF.2.2 x) (hb x).1)
        (mul_le_mul_of_nonneg_left (hG.2.2 x) (sub_nonneg.mpr (hb x).2))
      _ = 1 := by ring

lemma cutoff_partition_flux_le {E : Set Torus} (hP : perimeter E ≠ ⊤)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      (w x * divergence F x + (1 - w x) * divergence G x)) ≤
    (perimeter E).toReal + 2 *
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
  let H : Cover → Cover := fun x ↦ w x • F x + (1 - w x) • G x
  have hH : AdmissibleField H := admissible_convex_cutoff hw hp hb hF hG
  have hd (x) : divergence H x = w x * divergence F x +
      (1 - w x) * divergence G x + ⟪gradient w x, F x - G x⟫ := by
    have hwd : DifferentiableAt ℝ (fun y : Cover ↦ w y • F y) x := by
      convert! ((hw.smul hF.1).differentiable (by simp)) x using 1
      all_goals try with_reducible_and_instances rfl
    have hgd : DifferentiableAt ℝ (fun y : Cover ↦ (1 - w y) • G y) x := by
      convert! (((show ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Cover ↦ 1 - w y) from contDiff_const.sub hw).smul hG.1).differentiable (by simp)) x using 1
      all_goals try with_reducible_and_instances rfl
    dsimp only [H]
    rw [divergence_add_fields hwd hgd,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
        (hF.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function ((show ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ 1 - w x)
        from contDiff_const.sub hw).differentiable (by simp)).differentiableAt
        (hG.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left, inner_sub_right]
    ring
  have hii : IntegrableOn (fun x ↦ ⟪gradient w x, F x - G x⟫)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous
      ((gradient_contDiff hw).continuous.inner (hF.1.continuous.sub hG.1.continuous))
      (fun n x ↦ by simp only [Pi.sub_apply, gradient_periodic hp, hF.2.1, hG.2.1])).mono_set inter_subset_left
  have hign : IntegrableOn (fun x ↦ ‖gradient w x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])).mono_set inter_subset_left
  have hiH := (integrableOn_divergence hH.1).mono_set (s := fundamentalCube ∩ quotientMap ⁻¹' E)
    inter_subset_left
  have heq : (fun x ↦ w x * divergence F x + (1 - w x) * divergence G x) =
      (fun x ↦ divergence H x - ⟪gradient w x, F x - G x⟫) := by
    funext x
    rw [hd]
    ring
  rw [heq, integral_sub hiH hii]
  have hflux := (le_abs_self _).trans (abs_flux_le_perimeter hP hH)
  have herror : -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ⟪gradient w x, F x - G x⟫) ≤
      2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hii.neg (hign.const_mul 2)
    intro x
    have hg : ‖F x - G x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hF.2.2 x, hG.2.2 x])
    calc
      _ ≤ |⟪gradient w x, F x - G x⟫| := neg_le_abs _
      _ ≤ ‖gradient w x‖ * ‖F x - G x‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := by nlinarith [norm_nonneg (gradient w x)]
  linarith

end CubicTorus

namespace CubicTorus

lemma smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.zero_of_nonpos hx]
  exact Real.smoothTransition.nonneg y

lemma smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.one_of_one_le hx]
  exact Real.smoothTransition.le_one y

lemma smoothTransition_exists_deriv_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases h0 : x < 0
  · rw [smoothTransition_deriv_zero_of_nonpos h0.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  by_cases h1 : 1 < x
  · rw [smoothTransition_deriv_zero_of_one_le h1.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  exact (hM x ⟨le_of_not_gt h0, le_of_not_gt h1⟩).trans (le_max_left _ _)

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

lemma sublevelCutoff_periodic {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t ε : ℝ) :
    ∀ n x, sublevelCutoff q t ε (x + latticeVector n) = sublevelCutoff q t ε x := by
  intro n x
  simp only [sublevelCutoff, hp]

lemma sublevelCutoff_mem_Icc (q : Cover → ℝ) (t ε : ℝ) (x : Cover) :
    sublevelCutoff q t ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma fderiv_sublevelCutoff {q : Cover → ℝ} {x : Cover}
    (hq : DifferentiableAt ℝ q x) (t ε : ℝ) :
    fderiv ℝ (sublevelCutoff q t ε) x =
      (deriv Real.smoothTransition ((t - q x) / ε) / ε) • (-fderiv ℝ q x) := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((t - q x) / ε) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) _
  have hi := (hq.hasFDerivAt.const_sub t).const_smul ε⁻¹
  have hi' : HasFDerivAt (fun y : Cover ↦ (t - q y) / ε)
      (ε⁻¹ • (-fderiv ℝ q x)) x := by
    convert! hi using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp [div_eq_inv_mul]
  have ho := hd.hasDerivAt.comp_hasFDerivAt x hi'
  calc
    _ = deriv Real.smoothTransition ((t - q x) / ε) • (ε⁻¹ • (-fderiv ℝ q x)) := by
      convert! ho.fderiv using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by simp only [div_eq_mul_inv, smul_smul]

lemma norm_gradient_eq_norm_fderiv (f : Cover → ℝ) (x : Cover) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Cover).symm.norm_map _

lemma sublevelCutoff_gradient_bound {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {K : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover) :
    ‖gradient (sublevelCutoff q t ε) x‖ ≤ (K / ε) * ‖gradient q x‖ := by
  rw [norm_gradient_eq_norm_fderiv, fderiv_sublevelCutoff (hq x),
    norm_smul, norm_div, norm_neg, Real.norm_of_nonneg hε.le,
    norm_gradient_eq_norm_fderiv]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hK _) hε.le) (norm_nonneg _)

lemma sublevelCutoff_gradient_zero {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover)
    (hx : q x ≤ t - ε ∨ t ≤ q x) :
    gradient (sublevelCutoff q t ε) x = 0 := by
  apply (InnerProductSpace.toDual ℝ Cover).injective
  simp only [gradient, LinearIsometryEquiv.apply_symm_apply, map_zero]
  rw [fderiv_sublevelCutoff (hq x)]
  have hd : deriv Real.smoothTransition ((t - q x) / ε) = 0 := by
    rcases hx with hx | hx
    · apply smoothTransition_deriv_zero_of_one_le
      apply (le_div_iff₀ hε).2
      linarith
    · exact smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)
  rw [hd, zero_div, zero_smul]

end CubicTorus

namespace CubicTorus

lemma perimeter_partition_le_of_flux_bound {E B : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hB : MeasurableSet B) {C : ℝ}
    (hb : ∀ (F G : Cover → Cover), AdmissibleField F → AdmissibleField G →
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x) ≤ C) :
    FinitePerimeter (E ∩ B) ∧ FinitePerimeter (E \ B) ∧
      (perimeter (E ∩ B)).toReal + (perimeter (E \ B)).toReal ≤ C := by
  have ha : perimeter (E ∩ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, add_zero] using hb F (fun _ ↦ 0) hF admissible_zero
  have hd : perimeter (E \ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro G
    apply iSup_le
    intro hG
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, zero_add] using hb (fun _ ↦ 0) G admissible_zero hG
  refine ⟨⟨hE.inter hB.nullMeasurableSet, ha.trans_lt ENNReal.ofReal_lt_top⟩,
    ⟨hE.diff hB.nullMeasurableSet, hd.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hf⟩ := exists_admissible_flux_gt (E ∩ B) (half_pos hε)
  obtain ⟨G, hG, hg⟩ := exists_admissible_flux_gt (E \ B) (half_pos hε)
  linarith [hb F G hF hG]

lemma partition_flux_tendsto {E B : Set Torus} (hB : MeasurableSet B)
    {w : ℕ → Cover → ℝ} (hw : ∀ n, Continuous (w n))
    (hb : ∀ n x, w n x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (characteristic B (quotientMap x))))
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    Tendsto (fun n ↦ ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      w n x * divergence F x + (1 - w n x) * divergence G x) atTop
      (𝓝 ((∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x)) := by
  have hiF := (integrableOn_divergence hF.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hiG := (integrableOn_divergence hG.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E))
    (bound := fun x ↦ |divergence F x| + |divergence G x|)
    (F := fun n x ↦ w n x * divergence F x + (1 - w n x) * divergence G x)
    (f := fun x ↦ characteristic B (quotientMap x) * divergence F x +
      (1 - characteristic B (quotientMap x)) * divergence G x)
    (fun n ↦ (((hw n).mul (continuous_divergence hF.1)).add
      ((continuous_const.sub (hw n)).mul (continuous_divergence hG.1))).aestronglyMeasurable)
    (hiF.abs.add hiG.abs) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ (ht x |>.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub (ht x)).mul tendsto_const_nhds))
  · have heq : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        characteristic B (quotientMap x) * divergence F x +
        (1 - characteristic B (quotientMap x)) * divergence G x) =
        (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x := by
      have hp (x : Cover) : characteristic B (quotientMap x) * divergence F x +
          (1 - characteristic B (quotientMap x)) * divergence G x =
          (quotientMap ⁻¹' B).indicator (divergence F) x +
          (quotientMap ⁻¹' Bᶜ).indicator (divergence G) x := by
        classical
        by_cases hx : quotientMap x ∈ B <;> simp [characteristic, hx]
      simp_rw [hp]
      rw [integral_add (hiF.indicator (measurable_quotientMap hB))
        (hiG.indicator (measurable_quotientMap hB.compl)),
        integral_indicator (measurable_quotientMap hB),
        integral_indicator (measurable_quotientMap hB.compl),
        Measure.restrict_restrict (measurable_quotientMap hB),
        Measure.restrict_restrict (measurable_quotientMap hB.compl)]
      rw [show (quotientMap ⁻¹' B) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B) by ext x; simp only [mem_inter_iff, mem_preimage]; tauto,
        show (quotientMap ⁻¹' Bᶜ) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E \ B) by ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]; tauto]
    exact heq ▸ hh
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ |w n x * divergence F x| + |(1 - w n x) * divergence G x| := abs_add_le _ _
      _ = w n x * |divergence F x| + (1 - w n x) * |divergence G x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hb n x).1,
          abs_of_nonneg (sub_nonneg.mpr (hb n x).2)]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hb n x).2)
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hb n x).1]))

end CubicTorus

namespace CubicTorus

lemma measurableSet_sublevelRegion {q : Cover → ℝ} (hq : Measurable q) (t : ℝ) :
    MeasurableSet (sublevelRegion q t) :=
  measurableSet_lt (hq.comp measurable_representative) measurable_const

lemma mem_sublevelRegion_quotient {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t : ℝ) (x : Cover) :
    quotientMap x ∈ sublevelRegion q t ↔ q x < t := by
  simp only [sublevelRegion, mem_ofPred_eq, periodic_representative hp]

lemma sublevelRegion_mono (q : Cover → ℝ) : Monotone (sublevelRegion q) := by
  intro s t hst z hz
  exact hz.trans_le hst

lemma sublevelVolume_mono (E : Set Torus) (q : Cover → ℝ) :
    Monotone (sublevelVolume E q) := by
  intro s t hst
  exact measureReal_mono (inter_subset_inter_right E (sublevelRegion_mono q hst))

lemma sublevelCutoff_gradient_integral_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {K M t ε : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M) (hε : 0 < ε) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ‖gradient (sublevelCutoff q t ε) x‖) ≤
      K * M * ((sublevelVolume E q t - sublevelVolume E q (t - ε)) / ε) := by
  let A := sublevelRegion q t \ sublevelRegion q (t - ε)
  have hmA : MeasurableSet A := (measurableSet_sublevelRegion hq.continuous.measurable t).diff
    (measurableSet_sublevelRegion hq.continuous.measurable (t - ε))
  have hqdiff := hq.differentiable (by simp)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hb (x : Cover) : ‖gradient (sublevelCutoff q t ε) x‖ ≤
      (quotientMap ⁻¹' A).indicator (fun _ ↦ K * M / ε) x := by
    classical
    by_cases hx : x ∈ quotientMap ⁻¹' A
    · rw [Set.indicator_of_mem hx]
      have hxt : q x < t := (mem_sublevelRegion_quotient hp t x).1 hx.1
      calc
        _ ≤ (K / ε) * ‖gradient q x‖ := sublevelCutoff_gradient_bound hqdiff hK hε t x
        _ ≤ (K / ε) * M := mul_le_mul_of_nonneg_left (hgrad x hxt) (div_nonneg hK0 hε.le)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      rw [sublevelCutoff_gradient_zero hqdiff hε t x, norm_zero]
      have hn : ¬(q x < t ∧ ¬q x < t - ε) := by
        simpa only [A, mem_preimage, Set.mem_sdiff, mem_sublevelRegion_quotient hp] using hx
      rcases le_or_gt t (q x) with h | h
      · exact Or.inr h
      · exact Or.inl (le_of_lt (not_not.mp (fun hh ↦ hn ⟨h, hh⟩)))
  have hig : IntegrableOn (fun x ↦ ‖gradient (sublevelCutoff q t ε) x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff (sublevelCutoff_contDiff hq t ε)).continuous.norm
      (fun n x ↦ by rw [gradient_periodic (sublevelCutoff_periodic hp t ε)])).mono_set inter_subset_left
  have hic : IntegrableOn (fun _ : Cover ↦ K * M / ε)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous continuous_const (fun _ _ ↦ rfl)).mono_set inter_subset_left
  have hh := integral_mono hig (hic.indicator (measurable_quotientMap hmA)) hb
  rw [integral_indicator (measurable_quotientMap hmA),
    Measure.restrict_restrict (measurable_quotientMap hmA)] at hh
  have heq : quotientMap ⁻¹' A ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
      fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A) := by ext x; simp only [mem_inter_iff, mem_preimage]; tauto
  rw [heq, integral_const] at hh
  simp only [Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul] at hh
  change _ ≤ volume.real (fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A)) * (K * M / ε) at hh
  rw [← realVolume_lift (hE.inter hmA)] at hh
  have hsets : E ∩ A = (E ∩ sublevelRegion q t) \ (E ∩ sublevelRegion q (t - ε)) := by
    ext z; simp only [A, mem_inter_iff, Set.mem_sdiff]; tauto
  have hsubset : E ∩ sublevelRegion q (t - ε) ⊆ E ∩ sublevelRegion q t :=
    inter_subset_inter_right E (sublevelRegion_mono q (by linarith))
  rw [hsets, measureReal_sdiff hsubset
    (hE.inter (measurableSet_sublevelRegion hq.continuous.measurable (t - ε)))] at hh
  change _ ≤ (sublevelVolume E q t - sublevelVolume E q (t - ε)) * (K * M / ε) at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

namespace CubicTorus

lemma sublevelCutoff_tendsto {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (t : ℝ) (x : Cover) :
    Tendsto (fun n ↦ sublevelCutoff q t (ε n) x) atTop
      (𝓝 (characteristic (sublevelRegion q t) (quotientMap x))) := by
  classical
  by_cases hx : q x < t
  · have hmem := (mem_sublevelRegion_quotient hp t x).2 hx
    have he : ∀ᶠ n in atTop, sublevelCutoff q t (ε n) x = 1 := by
      filter_upwards [hεlim.eventually (gt_mem_nhds (sub_pos.mpr hx))] with n hn
      apply Real.smoothTransition.one_of_one_le
      apply (le_div_iff₀ (hε n)).2
      linarith
    rw [characteristic, indicator_of_mem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn ↦ hn.symm)
  · have hmem : quotientMap x ∉ sublevelRegion q t :=
      fun h ↦ hx ((mem_sublevelRegion_quotient hp t x).1 h)
    rw [characteristic, indicator_of_notMem hmem]
    have he (n) : sublevelCutoff q t (ε n) x = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hx)) (hε n).le
    simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

lemma tendsto_backward_quotient_of_hasDerivAt {m : ℝ → ℝ} {d t : ℝ}
    (hm : HasDerivAt m d t) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (m t - m (t - ε n)) / ε n) atTop (𝓝 d) := by
  have hlim : Tendsto (fun n ↦ t - ε n) atTop (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.sub hεlim, Eventually.of_forall fun n ↦ ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hε n]
  have hs := hm.tendsto_slope.comp hlim
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [Function.comp_apply, slope_def_field, show t - ε n - t = -(ε n) by ring, div_neg]
  ring

theorem perimeter_sublevel_partition {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume E q) d t) :
    FinitePerimeter (E ∩ sublevelRegion q t) ∧
    FinitePerimeter (E \ sublevelRegion q t) ∧
    (perimeter (E ∩ sublevelRegion q t)).toReal +
      (perimeter (E \ sublevelRegion q t)).toReal ≤ (perimeter E).toReal + 2 * K * M * d := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := measurableSet_sublevelRegion hq.continuous.measurable t
  apply perimeter_partition_le_of_flux_bound hE.nullMeasurableSet hb
  intro F G hF hG
  have hlim := partition_flux_tendsto (E := E) hb
    (fun n ↦ (sublevelCutoff_contDiff hq t (ε n)).continuous)
    (fun n x ↦ sublevelCutoff_mem_Icc q t (ε n) x)
    (sublevelCutoff_tendsto hp hε helim t) hF hG
  have hh := tendsto_backward_quotient_of_hasDerivAt hd hε helim
  have hrlim : Tendsto (fun n ↦ (perimeter E).toReal + 2 * K * M *
      ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) atTop
        (𝓝 ((perimeter E).toReal + 2 * K * M * d)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hh)
  apply le_of_tendsto_of_tendsto' hlim hrlim
  intro n
  calc
    _ ≤ (perimeter E).toReal + 2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ‖gradient (sublevelCutoff q t (ε n)) x‖ :=
      cutoff_partition_flux_le hP (sublevelCutoff_contDiff hq t (ε n))
        (sublevelCutoff_periodic hp t (ε n)) (sublevelCutoff_mem_Icc q t (ε n)) hF hG
    _ ≤ (perimeter E).toReal + 2 * (K * M *
        ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (sublevelCutoff_gradient_integral_le hE hq hp hK hgrad (hε n)) (show (0 : ℝ) ≤ 2 by norm_num))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma regionDistance_sdiff {E B : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (hB : NullMeasurableSet B torusVolume) :
    regionDistance E (E \ B) = torusVolume.real (E ∩ B) := by
  have heq (x : Torus) : ‖characteristic E x - characteristic (E \ B) x‖ =
      characteristic (E ∩ B) x := by
    classical
    by_cases he : x ∈ E <;> by_cases hb : x ∈ B <;> simp [characteristic, he, hb]
  unfold regionDistance
  simp_rw [heq]
  exact integral_characteristic (hE.inter hB)

theorem isMinimizerAt_sublevel_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (q : Cover → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) q → (∀ n x, q (x + latticeVector n) = q x) →
      ∀ K M t d : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume E q) d t → sublevelVolume E q t < η →
      (perimeter (E ∩ sublevelRegion q t)).toReal ≤
        C * sublevelVolume E q t + 2 * K * M * d := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η, C, hη, hC, ?_⟩
  intro q hq hp K M t d hK hgrad hd ht
  obtain ⟨_, hdiff, hpart⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad hd
  have hdist : regionDistance E (E \ sublevelRegion q t) = sublevelVolume E q t :=
    regionDistance_sdiff hmin.1.1 (measurableSet_sublevelRegion hq.continuous.measurable t).nullMeasurableSet
  have hcomp := hc (E \ sublevelRegion q t) hdiff (by rwa [hdist])
  rw [hdist] at hcomp
  linarith

theorem isMinimizerAt_sublevel_density_inequality {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C K : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 < K ∧
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x + latticeVector n) = q x) →
      ∀ᵐ t : ℝ, ∀ M : ℝ, (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
        sublevelVolume E q t < η → sublevelVolume E q t ≤ 1/2 →
        sublevelVolume E q t ^ (2 / 3 : ℝ) ≤
          12 * C * sublevelVolume E q t + 24 * K * M * deriv (sublevelVolume E q) t := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_sublevel_comparison hV hE hmin
  obtain ⟨K, hKpos, hK⟩ := smoothTransition_exists_deriv_bound
  refine ⟨η, C, K, hη, hC, hKpos, ?_⟩
  intro q hq hp
  filter_upwards [(sublevelVolume_mono E q).ae_differentiableAt] with t ht
  intro M hgrad hm hhalf
  have hcomp := hc q hq hp K M t (deriv (sublevelVolume E q) t) hK hgrad ht.hasDerivAt hm
  obtain ⟨hcut, _, _⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad ht.hasDerivAt
  have hiso := bv_isoperimetric_small hcut hhalf
  change sublevelVolume E q t ^ (2 / 3 : ℝ) ≤ _ at hiso
  linarith

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

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCore := by
  exact radialBump.contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport radialCore :=
  radialBump.hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport radialCore ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport (radialBump : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [radialBump.tsupport_eq] at hs
  have hnorm : ‖x - cubeCenter‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans hnorm
  change ‖x i - (1 / 2 : ℝ)‖ ≤ 1 / 3 at hb
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialSquared :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    radialSquared (x + latticeVector n) = radialSquared x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    radialSquared x = 1 - radialBump x * (1 - ‖x - cubeCenter‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - cubeCenter‖ < 1 / 4) :
    radialSquared =ᶠ[𝓝 x] (fun y ↦ ‖y - cubeCenter‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := radialBump.eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball cubeCenter radialBump.rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    radialSquared x < t ↔ ‖x - cubeCenter‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - cubeCenter)
  have hb0 : 0 ≤ radialBump x := radialBump.nonneg
  have hb1 : radialBump x ≤ 1 := radialBump.le_one
  have he (h : ‖x - cubeCenter‖ ^ 2 < 1 / 16) : radialBump x = 1 := by
    apply radialBump.one_of_mem_closedBall
    change dist x cubeCenter ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - cubeCenter‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - cubeCenter‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion radialSquared (r ^ 2) = cubeBall r := by
  ext z
  change radialSquared (representative z) < r ^ 2 ↔
    dist (representative z) cubeCenter < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma norm_gradient_radialSquared_of_mem_cube {x : Cover} (hx : x ∈ fundamentalCube)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (hxt : radialSquared x < r ^ 2) :
    ‖gradient radialSquared x‖ ≤ 2 * r := by
  have hnormsq := (radialSquared_sublevel_iff hx (by nlinarith)).1 hxt
  have hnorm : ‖x - cubeCenter‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr).mp hnormsq
  rw [norm_gradient_eq_norm_fderiv,
    (radialSquared_eventuallyEq_norm_sq (hnorm.trans_le hsmall)).fderiv_eq]
  have he : (fun y : Cover ↦ ‖y - cubeCenter‖ ^ 2) =
      (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) := by simp only [sub_eq_add_neg]
  rw [he]
  have hf : fderiv ℝ (fun y : Cover ↦ ‖y + -cubeCenter‖ ^ 2) x =
      fderiv ℝ (fun y : Cover ↦ ‖y‖ ^ 2) (x + -cubeCenter) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Cover ↦ ‖y‖ ^ 2) (x := x) (-cubeCenter) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hf, fderiv_norm_sq_apply, two_smul]
  calc
    _ ≤ ‖innerSL ℝ (x + -cubeCenter)‖ + ‖innerSL ℝ (x + -cubeCenter)‖ := norm_add_le _ _
    _ = 2 * ‖x - cubeCenter‖ := by rw [innerSL_apply_norm]; simp only [sub_eq_add_neg]; ring
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm.le (by norm_num)

lemma norm_gradient_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (x : Cover)
    (hxt : radialSquared x < r ^ 2) : ‖gradient radialSquared x‖ ≤ 2 * r := by
  have he := periodic_representative radialSquared_periodic x
  have hg := periodic_representative (f := gradient radialSquared)
    (fun n y ↦ gradient_periodic radialSquared_periodic n y) x
  rw [← hg]
  exact norm_gradient_radialSquared_of_mem_cube (representative_mem_fundamentalCube _) hr hsmall (by rwa [he])

end CubicTorus

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

lemma volume_torusBall (a : Torus) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball a r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  have he : Metric.ball a r = (fun z : Torus ↦ z + -a) ⁻¹' Metric.ball 0 r := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero]
  rw [he, volume_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet, volume_centeredBall hr0 hr1]

lemma localRadialSquared_contDiff (a : Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (localRadialSquared a) :=
  radialSquared_contDiff.comp (contDiff_id.add contDiff_const)

lemma localRadialSquared_periodic (a : Torus) (n : Fin 3 → ℤ) (x : Cover) :
    localRadialSquared a (x + latticeVector n) = localRadialSquared a x := by
  unfold localRadialSquared
  rw [show x + latticeVector n + representative (quotientMap cubeCenter - a) =
    (x + representative (quotientMap cubeCenter - a)) + latticeVector n by abel]
  exact radialSquared_periodic n _

lemma sublevelRegion_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4) :
    sublevelRegion (localRadialSquared a) (r ^ 2) = Metric.ball a r := by
  ext z
  have hrep := periodic_representative radialSquared_periodic
    (representative z + representative (quotientMap cubeCenter - a))
  rw [quotientMap_add, quotientMap_representative, quotientMap_representative] at hrep
  change radialSquared (representative z + representative (quotientMap cubeCenter - a)) < r ^ 2 ↔ _
  rw [← hrep]
  change z + (quotientMap cubeCenter - a) ∈ sublevelRegion radialSquared (r ^ 2) ↔ _
  rw [sublevelRegion_radialSquared hr hs, cubeBall_eq_metricBall]
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z + (quotientMap cubeCenter - a) - quotientMap cubeCenter = z - a by abel]

lemma norm_gradient_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4)
    (x : Cover) (hx : localRadialSquared a x < r ^ 2) :
    ‖gradient (localRadialSquared a) x‖ ≤ 2 * r := by
  rw [norm_gradient_eq_norm_fderiv]
  have he : fderiv ℝ (localRadialSquared a) x =
      fderiv ℝ radialSquared (x + representative (quotientMap cubeCenter - a)) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := radialSquared) (x := x)
      (representative (quotientMap cubeCenter - a)) using 1
    all_goals try with_reducible_and_instances rfl
  rw [he, ← norm_gradient_eq_norm_fderiv]
  exact norm_gradient_radialSquared hr hs _ hx

lemma sublevelVolume_localRadialSquared_le (E : Set Torus) (a : Torus) {r t : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1 / 4) (ht : t ≤ r ^ 2) :
    sublevelVolume E (localRadialSquared a) t ≤ (2 * r) ^ 3 := by
  calc
    _ ≤ sublevelVolume E (localRadialSquared a) (r ^ 2) := sublevelVolume_mono E _ ht
    _ ≤ torusVolume.real (Metric.ball a r) := by
      unfold sublevelVolume
      rw [sublevelRegion_localRadialSquared a hr hs]
      exact measureReal_mono inter_subset_right
    _ = r ^ 3 * (Real.pi * 4 / 3) := by
      rw [Measure.real_def, volume_torusBall a hr (by linarith), ENNReal.toReal_ofReal (by positivity)]
    _ ≤ (2 * r) ^ 3 := by nlinarith [Real.pi_lt_four, pow_nonneg hr 3]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CubicTorus

theorem monotone_density_root_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    T / (6 * c) ≤ m T ^ (1 / 3 : ℝ) := by
  let g : ℝ → ℝ := fun x ↦ m x ^ (1 / 3 : ℝ)
  have hg : Monotone g := fun x y hxy ↦ Real.rpow_le_rpow (hm0 x) (hm hxy) (by norm_num)
  have hderiv : ∀ᵐ x : ℝ, x ∈ Ioo 0 T → 1 / (6 * c) ≤ deriv g x := by
    filter_upwards [hm.ae_differentiableAt, hode] with x hmx hode
    intro hx
    have hmx0 : 0 < m x := hpos x ⟨hx.1, hx.2.le⟩
    have hp : 0 < m x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hmx0 _
    have hgderiv : HasDerivAt g ((1 / 3 : ℝ) * m x ^ (-2 / 3 : ℝ) * deriv m x) x := by
      convert! (Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hmx0.ne')).comp x hmx.hasDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [g, Function.comp_def]
    have hpower : m x ^ (1 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = m x := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have hpower' : m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hmx0]
      norm_num
    have he : deriv g x * m x ^ (2 / 3 : ℝ) = deriv m x / 3 := by
      rw [hgderiv.deriv]
      calc
        _ = (m x ^ (-2 / 3 : ℝ) * m x ^ (2 / 3 : ℝ)) * deriv m x / 3 := by ring
        _ = _ := by rw [hpower']; ring
    have hbr : b * m x ^ (1 / 3 : ℝ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (hroot x ⟨hx.1, hx.2.le⟩) hb).trans hab
    have hbm : b * m x ≤ m x ^ (2 / 3 : ℝ) / 2 := by
      have hh := mul_le_mul_of_nonneg_right hbr hp.le
      rw [mul_assoc, hpower] at hh
      linarith
    have hineq := hode hx
    have hbound : (1 - 6 * c * deriv g x) * m x ^ (2 / 3 : ℝ) ≤ 0 := by
      nlinarith [he]
    have hbound' := nonpos_of_mul_nonpos_left hbound hp
    apply (div_le_iff₀ (by positivity : 0 < 6 * c)).2
    nlinarith
  have hlower (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (T - s) / (6 * c) ≤ g T := by
    have hgi : IntervalIntegrable (deriv g) volume s T := (hg.monotoneOn _).intervalIntegrable_deriv
    have hint := (hg.monotoneOn _).intervalIntegral_deriv_mem_uIcc (a := s) (b := T)
    rw [uIcc_of_le (sub_nonneg.mpr (hg hsT))] at hint
    have haeb : ∀ᵐ x ∂volume.restrict (Icc s T), 1 / (6 * c) ≤ deriv g x := by
      filter_upwards [ae_restrict_of_ae hderiv,
        ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ T} = 0))] with x hd hx hne
      exact hd ⟨hs.trans_le hx.1, hx.2.lt_of_ne hne⟩
    have hil := intervalIntegral.integral_mono_ae_restrict hsT
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ 1 / (6 * c)) volume s T)
      hgi haeb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hil
    simp only [mul_one_div] at hil
    have hgs : 0 ≤ g s := Real.rpow_nonneg (hm0 s) _
    linarith [hint.2]
  let s : ℕ → ℝ := fun n ↦ T / ((n : ℝ) + 1)
  have hs (n) : 0 < s n := by dsimp [s]; positivity
  have hsT (n) : s n ≤ T := by
    dsimp [s]
    exact div_le_self hT.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := T)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have hlim : Tendsto (fun n ↦ (T - s n) / (6 * c)) atTop (𝓝 (T / (6 * c))) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hs0).div_const (6 * c)
  exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds (fun n ↦ hlower (s n) (hs n) (hsT n))

theorem monotone_density_lower {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : ∀ x, 0 ≤ m x) {T a b c : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hc : 0 < c)
    (hab : b * a ≤ 1 / 2)
    (hpos : ∀ x ∈ Ioc 0 T, 0 < m x)
    (hroot : ∀ x ∈ Ioc 0 T, m x ^ (1 / 3 : ℝ) ≤ a)
    (hode : ∀ᵐ x : ℝ, x ∈ Ioo 0 T →
      m x ^ (2 / 3 : ℝ) ≤ b * m x + c * deriv m x) :
    (T / (6 * c)) ^ 3 ≤ m T := by
  have hh := monotone_density_root_lower hm hm0 hT hb hc hab hpos hroot hode
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ T / (6 * c)) hh 3
  have he : (m T ^ (1 / 3 : ℝ)) ^ 3 = m T := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (hm0 T) (by norm_num : (3 : ℕ) ≠ 0)
  rwa [he] at hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_volume_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (∀ s : ℝ, 0 < s → 0 < torusVolume.real (E ∩ Metric.ball a s)) →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) := by
  obtain ⟨η, C, K, hη, hC, hK, hode⟩ := isMinimizerAt_sublevel_density_inequality hV hE hmin
  let R := min (1 / 4 : ℝ) (min (η / 16) (1 / (48 * (C + 1))))
  let c := (1 / (288 * K)) ^ 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨R, c, hR, hc, ?_⟩
  intro a r hr hrR hsupport
  have hrsmall : r ≤ 1 / 4 := hrR.trans (min_le_left _ _)
  have hrη : r ≤ η / 16 := hrR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r ≤ 1 / (48 * (C + 1)) := hrR.trans ((min_le_right _ _).trans (min_le_right _ _))
  let q := localRadialSquared a
  let m := sublevelVolume E q
  have hm : Monotone m := sublevelVolume_mono E q
  have hm0 (t) : 0 ≤ m t := ENNReal.toReal_nonneg
  have hupper {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ (2 * r) ^ 3 :=
    sublevelVolume_localRadialSquared_le E a hr.le hrsmall ht
  have hroot {t : ℝ} (ht : t ≤ r ^ 2) : m t ^ (1 / 3 : ℝ) ≤ 2 * r := by
    have hh := Real.rpow_le_rpow (hm0 t) (hupper ht) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have he : ((2 * r) ^ 3) ^ (1 / 3 : ℝ) = 2 * r := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 2 * r) (by norm_num : (3 : ℕ) ≠ 0)
    rwa [he] at hh
  have heta {t : ℝ} (ht : t ≤ r ^ 2) : m t < η := by
    have hrpow : r ^ 3 ≤ r := by
      have hr1 : r ≤ 1 := by linarith
      have := pow_le_pow_left₀ hr.le hr1 2
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr this)]
    have hu := hupper ht
    nlinarith
  have hhalf {t : ℝ} (ht : t ≤ r ^ 2) : m t ≤ 1 / 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * r)
      (show 2 * r ≤ 1 / 2 by linarith) 3
    norm_num at hp
    linarith [hupper ht]
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 (r ^ 2)) : 0 < m t := by
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hsr : Real.sqrt t ≤ r := (Real.sqrt_le_iff).2 ⟨hr.le, ht.2⟩
    have he : m t = torusVolume.real (E ∩ Metric.ball a (Real.sqrt t)) := by
      change torusVolume.real (E ∩ sublevelRegion q t) = _
      have hh := sublevelRegion_localRadialSquared a hs0.le (hsr.trans hrsmall)
      rw [Real.sq_sqrt ht.1.le] at hh
      rw [hh]
    rw [he]
    exact hsupport _ hs0
  have haeb : ∀ᵐ t : ℝ, t ∈ Ioo 0 (r ^ 2) →
      m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + (48 * K * r) * deriv m t := by
    filter_upwards [hode q (localRadialSquared_contDiff a) (localRadialSquared_periodic a)] with t ht
    intro htr
    have hgrad (x : Cover) (hx : q x < t) : ‖gradient q x‖ ≤ 2 * r :=
      norm_gradient_localRadialSquared a hr.le hrsmall x (hx.trans htr.2)
    have hh := ht (2 * r) hgrad (heta htr.2.le) (hhalf htr.2.le)
    change m t ^ (2 / 3 : ℝ) ≤ 12 * C * m t + 24 * K * (2 * r) * deriv m t at hh
    nlinarith [hh]
  have hab : (12 * C) * (2 * r) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 48 * (C + 1))).1 hrC
    nlinarith
  have hlower := monotone_density_lower hm hm0 (sq_pos_of_pos hr)
    (show 0 ≤ 12 * C by positivity) (show 0 < 48 * K * r by positivity) hab hpos
    (fun t ht ↦ hroot ht.2) haeb
  have he : (r ^ 2 / (6 * (48 * K * r))) ^ 3 = c * r ^ 3 := by
    dsimp only [c]
    field_simp
    ring
  rw [he] at hlower
  change _ ≤ torusVolume.real (E ∩ sublevelRegion (localRadialSquared a) (r ^ 2)) at hlower
  rwa [sublevelRegion_localRadialSquared a hr.le hrsmall] at hlower

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

theorem isMinimizerAt_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ a ∈ volumeSupport E ∩ volumeSupport Eᶜ,
      ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r) ∧
      c * r ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a r) := by
  obtain ⟨R₁, c₁, hR₁, hc₁, hd₁⟩ := isMinimizerAt_volume_density hV hE hmin
  have hVc : 1 - V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2], by linarith [hV.1]⟩
  obtain ⟨R₂, c₂, hR₂, hc₂, hd₂⟩ := isMinimizerAt_volume_density hVc hE.compl
    ((isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hmin)
  refine ⟨min R₁ R₂, min c₁ c₂, lt_min hR₁ hR₂, lt_min hc₁ hc₂, ?_⟩
  intro a ha r hr hrR
  constructor
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hd₁ a r hr (hrR.trans (min_le_left _ _)) ((mem_volumeSupport_iff E a).1 ha.1))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
      (hd₂ a r hr (hrR.trans (min_le_right _ _)) ((mem_volumeSupport_iff Eᶜ a).1 ha.2))

instance torusVolume_doubling : IsUnifLocDoublingMeasure torusVolume := by
  refine ⟨27, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))] with r hr hs a
  have hrpos : 0 < r := hr
  change r < 1 / 6 at hs
  calc
    torusVolume (Metric.closedBall a (2 * r)) ≤ torusVolume (Metric.ball a (3 * r)) :=
      measure_mono (Metric.closedBall_subset_ball (by linarith))
    _ = (27 : ℝ≥0∞) * torusVolume (Metric.ball a r) := by
      rw [volume_torusBall a (by positivity) (by linarith),
        volume_torusBall a hrpos.le (by linarith), ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
      congr 1
      ring
    _ ≤ (27 : ℝ≥0∞) * torusVolume (Metric.closedBall a r) := by
      gcongr
      exact Metric.ball_subset_closedBall

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma integral_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) {f : Torus → ℝ}
    (hf : Measurable f) :
    (∫ x, f x ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, f (normalProjection z) ∂(μ : Measure NormalBundle) := by
  change (∫ x, f x ∂Measure.map normalProjection (μ : Measure NormalBundle)) = _
  exact integral_map normalProjection_continuous.measurable.aemeasurable hf.aestronglyMeasurable

lemma integral_spatialNormalMeasure_periodic (μ : FiniteMeasure NormalBundle)
    {w : Cover → ℝ} (hw : Continuous w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) :
    (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, w z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_spatialNormalMeasure μ (f := fun x ↦ w (representative x))
    (hw.measurable.comp measurable_representative)]
  congr 1
  ext z
  exact periodic_representative hp z.1

lemma spatialNormalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) := by
  rw [integral_spatialNormalMeasure_periodic μ hw.continuous hp]
  exact normalMeasure_weightedPerimeter hμ hw hp hn

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma sublevelCutoff_eq_one {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : q x ≤ t - ε) : sublevelCutoff q t ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by linarith)

lemma divergence_cutoff_zero {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {t ε : ℝ} (hε : 0 < ε) {x : Cover} (hx : t ≤ q x) :
    divergence (fun y ↦ sublevelCutoff q t ε y • F y) x = 0 := by
  rw [divergence_smul_function ((sublevelCutoff_contDiff hq t ε).differentiable (by simp) x)
    (hF.differentiable (by simp) x), sublevelCutoff_eq_zero hε hx,
    sublevelCutoff_gradient_zero (hq.differentiable (by simp)) hε t x (Or.inr hx)]
  simp

lemma admissible_sublevelCutoff {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {F : Cover → Cover}
    (hF : AdmissibleField F) (t ε : ℝ) :
    AdmissibleField (fun x ↦ sublevelCutoff q t ε x • F x) := by
  have hh := admissible_convex_cutoff (sublevelCutoff_contDiff hq t ε)
    (sublevelCutoff_periodic hp t ε) (sublevelCutoff_mem_Icc q t ε) hF admissible_zero
  simpa only [smul_zero, add_zero] using hh

lemma weightedPerimeter_sublevelCutoff_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {t ε : ℝ} (hε : 0 < ε) :
    weightedPerimeter E (sublevelCutoff q t ε) ≤ perimeter (E ∩ sublevelRegion q t) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have he : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ sublevelRegion q t),
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))
      (inter_subset_inter_right _ (preimage_mono inter_subset_left))
    intro x hx
    apply divergence_cutoff_zero hq hF.1 hε
    by_contra hn
    apply hx.2
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    exact (mem_sublevelRegion_quotient hp t x).2 (lt_of_not_ge hn)
  rw [he]
  exact le_iSup₂_of_le (fun x ↦ sublevelCutoff q t ε x • F x)
    (admissible_sublevelCutoff hq hp hF t ε) le_rfl

lemma spatialNormalMeasure_sublevel_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {s t : ℝ} (hst : s < t)
    (hP : perimeter (E ∩ sublevelRegion q t) ≠ ⊤) :
    (spatialNormalMeasure μ : Measure Torus).real (sublevelRegion q s) ≤
      (perimeter (E ∩ sublevelRegion q t)).toReal := by
  let σ : Measure Torus := spatialNormalMeasure μ
  let w := sublevelCutoff q t (t - s)
  let B := sublevelRegion q s
  have hB : MeasurableSet B := measurableSet_sublevelRegion hq.continuous.measurable s
  have hwb (x : Cover) : w x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (t - s) x
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := sublevelCutoff_contDiff hq t (t - s)
  have hwp : ∀ n x, w (x + latticeVector n) = w x := sublevelCutoff_periodic hp t (t - s)
  have hi : Integrable (fun x ↦ w (representative x)) σ :=
    Integrable.of_bound (hw.continuous.measurable.comp measurable_representative).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hwb _).1]
        exact (hwb _).2)
  have hminor (x : Torus) : B.indicator (fun _ ↦ (1 : ℝ)) x ≤ w (representative x) := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact le_of_eq (sublevelCutoff_eq_one (sub_pos.mpr hst) (by
        have hh : q (representative x) < s := hx
        linarith)).symm
    · rw [indicator_of_notMem hx]
      exact (hwb _).1
  have hm : σ.real B ≤ ∫ x, w (representative x) ∂σ := by
    have hh := integral_mono ((integrable_const (1 : ℝ)).indicator hB) hi hminor
    simpa only [integral_indicator hB, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] using hh
  have hpbound := weightedPerimeter_sublevelCutoff_le hE hq hp (t := t) (sub_pos.mpr hst)
  rw [spatialNormalMeasure_weightedPerimeter hμ hw hwp (fun x ↦ (hwb x).1)] at hpbound
  have hnonneg : 0 ≤ ∫ x, w (representative x) ∂σ := integral_nonneg fun x ↦ (hwb _).1
  have hh := ENNReal.toReal_mono hP hpbound
  rw [ENNReal.toReal_ofReal hnonneg] at hh
  exact hm.trans hh

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

lemma smoothApprox_zero_outside_ball {g : Cover → ℝ} {a : Torus} {r s : ℝ}
    (hz : ∀ x, quotientMap x ∉ Metric.ball a r → g x = 0) (n : ℕ)
    (hn : (mollifier n).rOut ≤ s) {x : Cover}
    (hx : quotientMap x ∉ Metric.ball a (r + s)) : smoothApprox g n x = 0 := by
  rw [smoothApprox, convolution_def]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : (mollifier n).normed volume y = 0
  · simp [hy]
  have hyn : ‖y‖ < (mollifier n).rOut := by
    have hh : y ∈ Function.support ((mollifier n).normed volume) := hy
    rw [(mollifier n).support_normed_eq] at hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hxy : quotientMap (x - y) ∉ Metric.ball a r := by
    intro hmem
    apply hx
    change dist (quotientMap x) a < r + s
    have ht := dist_triangle (quotientMap x) (quotientMap (x - y)) a
    have he : dist (quotientMap x) (quotientMap (x - y)) = ‖quotientMap y‖ := by
      rw [dist_eq_norm, quotientMap_sub, sub_sub_cancel]
    rw [he] at ht
    have hm : dist (quotientMap (x - y)) a < r := hmem
    linarith [norm_quotientMap_le y]
  simp [ContinuousLinearMap.lsmul_apply, hz (x - y) hxy]

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isNormalMeasure_compl {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure Eᶜ (μ.map reverseNormal) := by
  constructor
  · have hm : ((μ.map reverseNormal).mass : ℝ) = (μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal
        (Measure.map_apply continuous_reverseNormal.measurable MeasurableSet.univ
          (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ, FiniteMeasure.mass, FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map, Measure.real, ENNReal.toReal] using hh
    rw [hm, hμ.1, perimeter_compl hE.nullMeasurableSet]
  · intro F hF
    change (∫ z, normalTest F hF.1.continuous z
      ∂Measure.map reverseNormal (μ : Measure NormalBundle)) = _
    rw [integral_map continuous_reverseNormal.measurable.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable]
    change (∫ z, ⟪-(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
    simp_rw [inner_neg_left, integral_neg]
    rw [integral_divergence_compl hE.nullMeasurableSet hF, ← hμ.2 F hF]
    rfl

lemma spatialNormalMeasure_reverse (μ : FiniteMeasure NormalBundle) :
    spatialNormalMeasure (μ.map reverseNormal) = spatialNormalMeasure μ := by
  apply Subtype.ext
  change Measure.map normalProjection (Measure.map reverseNormal (μ : Measure NormalBundle)) = _
  rw [Measure.map_map normalProjection_continuous.measurable continuous_reverseNormal.measurable]
  rfl

lemma perimeter_eq_zero_of_volume_eq_zero {E : Set Torus} (hE : torusVolume E = 0) :
    perimeter E = 0 := by
  rw [perimeter_congr_ae (ae_eq_empty.mpr hE), perimeter_empty]

lemma spatialNormalMeasure_support_subset_volumeSupport {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E := by
  intro a ha
  rw [mem_volumeSupport_iff]
  intro r hr
  by_contra! hv
  have hz : torusVolume (E ∩ Metric.ball a r) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hv ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  let s := min r (1 / 4 : ℝ)
  have hs : 0 < s := lt_min hr (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsr : s ≤ r := min_le_left _ _
  have hcut : perimeter (E ∩ sublevelRegion (localRadialSquared a) (s ^ 2)) = 0 := by
    rw [sublevelRegion_localRadialSquared a hs.le hs4]
    apply perimeter_eq_zero_of_volume_eq_zero
    apply measure_mono_null (inter_subset_inter_right E (Metric.ball_subset_ball hsr)) hz
  have hbound := spatialNormalMeasure_sublevel_le hE hμ (localRadialSquared_contDiff a)
    (localRadialSquared_periodic a) (s := (s / 2) ^ 2) (t := s ^ 2)
    (by nlinarith [sq_pos_of_pos hs]) (by rw [hcut]; exact ENNReal.zero_ne_top)
  rw [hcut, ENNReal.toReal_zero,
    sublevelRegion_localRadialSquared a (by positivity : 0 ≤ s / 2) (by linarith)] at hbound
  have hzero : (spatialNormalMeasure μ : Measure Torus) (Metric.ball a (s / 2)) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hbound ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  have hp := (Metric.nhds_basis_ball.mem_measureSupport.mp ha) (s / 2) (by positivity)
  exact hp.ne' hzero

lemma spatialNormalMeasure_support_subset_boundary {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E ∩ volumeSupport Eᶜ := by
  intro a ha
  refine ⟨spatialNormalMeasure_support_subset_volumeSupport hE hμ ha, ?_⟩
  have hh := spatialNormalMeasure_support_subset_volumeSupport hE.compl (isNormalMeasure_compl hE hμ)
  rw [spatialNormalMeasure_reverse] at hh
  exact hh ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma map_supportedMeasure (σ : FiniteMeasure Torus) :
    Measure.map Subtype.val (supportedMeasure σ) = (σ : Measure Torus) := by
  rw [supportedMeasure, map_comap_subtype_coe Measure.isClosed_support.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (Measure.support_mem_ae (μ := (σ : Measure Torus)))

lemma supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) :
    supportedMeasure σ (Metric.closedBall a r) =
      (σ : Measure Torus) (Metric.closedBall (a : Torus) r) := by
  have hh := Measure.map_apply (μ := supportedMeasure σ) measurable_subtype_coe
    (show MeasurableSet (Metric.closedBall (a : Torus) r) from Metric.isClosed_closedBall.measurableSet)
  rw [map_supportedMeasure σ] at hh
  exact hh.symm

lemma setIntegral_supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) (f : Torus → ℝ) :
    (∫ x in Metric.closedBall a r, f (x : Torus) ∂supportedMeasure σ) =
      ∫ x in Metric.closedBall (a : Torus) r, f x ∂(σ : Measure Torus) := by
  have hh := (MeasurableEmbedding.subtype_coe
    (Measure.isClosed_support (μ := (σ : Measure Torus))).measurableSet).setIntegral_map
    (μ := supportedMeasure σ) f (Metric.closedBall (a : Torus) r)
  rw [map_supportedMeasure σ] at hh
  exact hh.symm

lemma setAverage_supportedMeasure_closedBall (σ : FiniteMeasure Torus)
    (a : (σ : Measure Torus).support) (r : ℝ) (f : Torus → ℝ) :
    (⨍ x in Metric.closedBall a r, f (x : Torus) ∂supportedMeasure σ) =
      ⨍ x in Metric.closedBall (a : Torus) r, f x ∂(σ : Measure Torus) := by
  simp only [setAverage_eq, Measure.real_def, supportedMeasure_closedBall,
    setIntegral_supportedMeasure_closedBall]

theorem isMinimizerAt_supportedMeasure_doubling {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsUnifLocDoublingMeasure (supportedMeasure (spatialNormalMeasure μ)) := by
  obtain ⟨R₁, A, hR₁, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨R₂, c, hR₂, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let σ := spatialNormalMeasure μ
  let C : ℝ≥0 := ⟨9 * A / c, by positivity⟩
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show 0 < min (R₁ / 3) R₂ by positivity))]
    with r hr hrR a
  have hrpos : 0 < r := hr
  change r < min (R₁ / 3) R₂ at hrR
  have hru : 3 * r ≤ R₁ := by linarith [(lt_min_iff.mp hrR).1]
  have hrl : r ≤ R₂ := (lt_min_iff.mp hrR).2.le
  have ha : (a : Torus) ∈ volumeSupport E ∩ volumeSupport Eᶜ :=
    spatialNormalMeasure_support_subset_boundary hE hμ a.property
  have hupper := hu μ hμ (a : Torus) (3 * r) (by positivity) hru
  have hlower := hl μ hμ (a : Torus) ha r hrpos hrl
  have hub := (measureReal_mono
    (Metric.closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans hupper
  have hlb := hlower.trans (measureReal_mono Metric.ball_subset_closedBall)
  rw [supportedMeasure_closedBall, supportedMeasure_closedBall]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (σ : Measure Torus).real (Metric.closedBall (a : Torus) (2 * r)) ≤
    (9 * A / c) * (σ : Measure Torus).real (Metric.closedBall (a : Torus) r)
  have hh := mul_le_mul_of_nonneg_left hlb (show 0 ≤ 9 * A / c by positivity)
  have he : (9 * A / c) * (c * r ^ 2) = A * (3 * r) ^ 2 := by field_simp; ring
  rw [he] at hh
  exact hub.trans hh

theorem isMinimizerAt_normal_differentiation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hb : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ ≤ 1) :
    ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, ‖N x - N a‖
        ∂(spatialNormalMeasure μ : Measure Torus)) (𝓝[>] 0) (𝓝 0) := by
  let σ := spatialNormalMeasure μ
  let ν := supportedMeasure σ
  let := isMinimizerAt_supportedMeasure_doubling hV hE hmin hμ
  have hb' : ∀ᵐ (x : (σ : Measure Torus).support) ∂ν, ‖N (x : Torus)‖ ≤ 1 := by
    rw [← map_supportedMeasure σ,
      (MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet).ae_map_iff] at hb
    exact hb
  have hi : Integrable (fun x : (σ : Measure Torus).support ↦ N (x : Torus)) ν :=
    Integrable.of_bound (hN.comp measurable_subtype_coe).aestronglyMeasurable 1 hb'
  have hd := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub ν hi.locallyIntegrable 1
  have hh : ∀ᵐ a ∂Measure.map Subtype.val ν,
      Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, ‖N x - N a‖ ∂(σ : Measure Torus))
        (𝓝[>] 0) (𝓝 0) := by
    rw [(MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet).ae_map_iff]
    filter_upwards [hd] with a ha
    have hh := ha (fun _ : ℝ ↦ a) id tendsto_id
      (show ∀ᶠ r : ℝ in 𝓝[>] 0, a ∈ Metric.closedBall a (1 * id r) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact Metric.mem_closedBall_self (by simpa using le_of_lt hr))
    exact hh.congr' (Eventually.of_forall fun r ↦
      setAverage_supportedMeasure_closedBall σ a r (fun x ↦ ‖N x - N (a : Torus)‖))
  simpa only [ν, map_supportedMeasure] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVTangentialBlowup
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

lemma normalized_setIntegral_le_average (σ : FiniteMeasure Torus) (B : Set Torus)
    (g : Torus → ℝ) (hg : ∀ x, 0 ≤ g x) {r A : ℝ} (hr : 0 < r)
    (hu : (σ : Measure Torus).real B ≤ A * r ^ 2) :
    (∫ x in B, g x ∂(σ : Measure Torus)) / r ^ 2 ≤
      A * (⨍ x in B, g x ∂(σ : Measure Torus)) := by
  have hh := measure_smul_setAverage g (measure_ne_top (σ : Measure Torus) B)
  rw [smul_eq_mul] at hh
  have ha : 0 ≤ ⨍ x in B, g x ∂(σ : Measure Torus) := integral_nonneg hg
  calc
    _ = ((σ : Measure Torus).real B / r ^ 2) *
        (⨍ x in B, g x ∂(σ : Measure Torus)) := by rw [← hh]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hr)).2 hu) ha

lemma normalOscillation_nonneg (σ : FiniteMeasure Torus) (N : Torus → Cover)
    (c : Torus) (n : Cover) (r : ℝ) : 0 ≤ normalOscillation σ N c n r :=
  div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (sq_nonneg _)

theorem isMinimizerAt_normal_oscillation_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (normalOscillation (spatialNormalMeasure μ) N c (N c)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, A, hR, _, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hd := isMinimizerAt_normal_differentiation hV hE hmin hμ hN
    (hn.mono fun _ hx ↦ hx.le)
  filter_upwards [hd] with c hc
  apply squeeze_zero' (Eventually.of_forall (normalOscillation_nonneg _ _ _ _))
    (g := fun r ↦ (4 * A) * (⨍ x in Metric.closedBall c r,
      ‖N x - N c‖ ∂(spatialNormalMeasure μ : Measure Torus)))
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show 0 < R / 2 by positivity))]
      with r hr hrR
    have hrpos : 0 < r := hr
    have hrlt : r < R / 2 := hrR
    apply normalized_setIntegral_le_average _ _ _ (fun _ ↦ norm_nonneg _) hrpos
    have hh := (measureReal_mono
      (Metric.closedBall_subset_ball (by linarith : r < 2 * r))).trans
      (hu μ hμ c (2 * r) (by positivity) (by linarith : 2 * r ≤ R))
    calc
      _ ≤ A * (2 * r) ^ 2 := hh
      _ = _ := by ring
  · simpa only [mul_zero] using hc.const_mul (4 * A)

lemma integrable_norm_sub_normal {σ : FiniteMeasure Torus} {N : Torus → Cover}
    (hN : Measurable N) (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) :
    Integrable (fun x ↦ ‖N x - n‖) (σ : Measure Torus) := by
  apply Integrable.of_bound (hN.sub_const n).norm.aestronglyMeasurable (1 + ‖n‖)
  filter_upwards [hn] with x hx
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [hx] using norm_sub_le (N x) n

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma smoothApprox_nonneg {g : Cover → ℝ} (hg : ∀ x, 0 ≤ g x) (k : ℕ) (x : Cover) :
    0 ≤ smoothApprox g k x := by
  rw [smoothApprox, convolution_def]
  exact integral_nonneg fun y ↦ mul_nonneg ((mollifier k).nonneg_normed y) (hg _)

lemma flux_ordered_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in B, ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun x ↦ f x • a) x := by
  have hfa := hf.smul_const a
  rw [← normalMeasure_flux hμ hfa (fun m x ↦ by rw [hp])
    (show 0 < ‖a‖ + 1 by positivity) (fun x ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg a) (hb x)).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun x ↦ -(‖a‖ * ‖N x - n‖))
  have hg : Measurable g := (((hN.sub_const n).norm.const_mul _).neg).indicator hB
  have hi : Integrable g (spatialNormalMeasure μ : Measure Torus) :=
    (((integrable_norm_sub_normal hN hn n).const_mul _).neg).indicator hB
  have him : Integrable (fun z : NormalBundle ↦ g (normalProjection z))
      (μ : Measure NormalBundle) :=
    (integrable_map_measure hg.aestronglyMeasurable
      normalProjection_continuous.measurable.aemeasurable).mp hi
  have hnt := (normalTest _ hfa.continuous).continuous.integrable_of_hasCompactSupport
    (μ := (μ : Measure NormalBundle)) (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono_ae him hnt (show ∀ᵐ z ∂(μ : Measure NormalBundle),
      g (normalProjection z) ≤ normalTest (fun x ↦ f x • a) hfa.continuous z from by
    filter_upwards [hpolar] with z hz'
    by_cases hzB : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hzB, normalTest, ContinuousMap.coe_mk,
        real_inner_smul_right]
      change -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤ f z.1 * ⟪(z.2 : Cover), a⟫
      rw [← hz']
      have hn' := (abs_le.mp (abs_real_inner_le_norm (N (quotientMap z.1) - n) a)).1
      rw [inner_sub_left] at hn'
      have hf1 := (le_abs_self (f z.1)).trans (hb z.1)
      have hnonneg := mul_nonneg (norm_nonneg a) (norm_nonneg (N (quotientMap z.1) - n))
      have hm := mul_le_mul_of_nonneg_left (show -(‖a‖ * ‖N (quotientMap z.1) - n‖) ≤
        ⟪N (quotientMap z.1), a⟫ by nlinarith) (hf0 z.1)
      nlinarith
    · simp [g, hzB, normalTest, hz z.1 hzB])
  rw [← integral_spatialNormalMeasure μ hg] at hh
  simpa only [g, integral_indicator hB, integral_neg, integral_const_mul] using hh

theorem smooth_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x) := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x = 0 := by
      have hm : quotientMap (x + t • a) ∉ Metric.ball c r := by
        intro hx'
        apply hx
        change dist (quotientMap x) c < r + ‖a‖
        have hh := dist_triangle (quotientMap x) (quotientMap (x + t • a)) c
        have he : dist (quotientMap x) (quotientMap (x + t • a)) = ‖quotientMap (t • a)‖ := by
          rw [dist_eq_norm, quotientMap_add, sub_add_cancel_left, norm_neg]
        rw [he] at hh
        have hs : ‖t • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg a) ht.2
        have hx'' : dist (quotientMap (x + t • a)) c < r := hx'
        linarith [norm_quotientMap_le (t • a)]
      simp [g, hz _ hm]
    have hh := flux_ordered_lower_bound hμ hN hpolar hn hg hp' (fun x ↦ hb _)
      (fun x ↦ hf0 _) Metric.isOpen_ball.measurableSet hzero ha
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1, -(‖a‖ * ∫ x in Metric.ball c (r + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) := by simp
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a := by
      apply integral_mono_ae (integrable_const _) hi.integral_prod_right
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact ht t ht'
    _ = _ := by rw [← integral_integral_swap hi]; simp_rw [hFTC]

theorem measurable_test_ordered_translation_lower_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x) := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply ge_of_tendsto hi
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hnr
  exact smooth_test_ordered_translation_lower_bound hμ hN hpolar hn
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (smoothApprox_nonneg hg0 n) (fun x hx ↦ smoothApprox_zero_outside_ball hz n hnr hx) ha

lemma torus_test_ordered_translation_lower_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) (hg0 : ∀ x, 0 ≤ g x)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    -(‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_ordered_translation_lower_bound hμ hN hpolar hn (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) (fun x ↦ hg0 _) hs (fun x hx ↦ hz _ hx) ha

lemma orderDefect_nonneg (E : Set Torus) (a x : Torus) : 0 ≤ orderDefect E a x := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma orderDefect_bound (E : Set Torus) (a x : Torus) : |orderDefect E a x| ≤ 1 := by
  rcases characteristic_dichotomy E x with h | h <;>
    rcases characteristic_dichotomy E (x - a) with h' | h' <;> simp [orderDefect, h, h']

lemma measurable_orderDefect {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    Measurable (orderDefect E a) :=
  (measurable_characteristic hE).mul (measurable_const.sub
    ((measurable_characteristic hE).comp (measurable_id.sub_const _)))

theorem characteristic_ordered_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : Torus) {r s : ℝ} (hs : 0 < s) {n a : Cover} (ha : 0 ≤ ⟪n, a⟫) :
    (∫ x in Metric.ball c r, orderDefect E (quotientMap a) x ∂torusVolume) ≤
      ‖a‖ * ∫ x in Metric.ball c (r + s + ‖a‖),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let g : Torus → ℝ := (Metric.ball c r).indicator (orderDefect E (quotientMap a))
  have hg : Measurable g := (measurable_orderDefect hE _).indicator Metric.isOpen_ball.measurableSet
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using orderDefect_bound E (quotientMap a) x
    · simp [g, hx]
  have hg0 : ∀ x, 0 ≤ g x := indicator_nonneg fun _ _ ↦ orderDefect_nonneg _ _ _
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_ordered_translation_lower_bound hE hμ hN hpolar hn hg hb hg0 hs hz ha
  rw [integral_difference_test hE hg hb] at hh
  have heq (x) : (characteristic E (x - quotientMap a) - characteristic E x) * g x =
      -((Metric.ball c r).indicator (orderDefect E (quotientMap a)) x) := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E x with h | h <;>
        rcases characteristic_dichotomy E (x - quotientMap a) with h' | h' <;>
          simp [orderDefect, h, h']
    · simp [g, hx]
  simp_rw [heq] at hh
  rwa [integral_neg, integral_indicator Metric.isOpen_ball.measurableSet, neg_le_neg_iff] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem ordered_volume_product_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {U W : Set Torus} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUE : U ⊆ Eᶜ) (hWE : W ⊆ E) (c : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4)
    (hUB : U ⊆ Metric.ball c r) (hWB : W ⊆ Metric.ball c r) (n : Cover)
    (hordered : ∀ x ∈ U, ∀ z ∈ W, 0 ≤ ⟪n, shortestLift (z - x)⟫) :
    torusVolume.real U * torusVolume.real W ≤ 128 * r ^ 4 *
      ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  let f : Torus × Torus → ℝ := fun z ↦ characteristic U (z.2 - z.1) * characteristic W z.2
  have hfm : Measurable f :=
    ((measurable_characteristic hU).comp (measurable_snd.sub measurable_fst)).mul
      ((measurable_characteristic hW).comp measurable_snd)
  have hfb (z : Torus × Torus) : |f z| ≤ 1 := by
    dsimp [f]
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (characteristic_bound U _)).trans
      (characteristic_bound W _)
  have hfi : Integrable f (torusVolume.prod torusVolume) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)
  let I : Torus → ℝ := fun a ↦ ∫ x, f (a, x) ∂torusVolume
  have hIi : Integrable I torusVolume := hfi.integral_prod_left
  have hIeq : (∫ a, I a ∂torusVolume) = torusVolume.real U * torusVolume.real W := by
    rw [show (∫ a, I a ∂torusVolume) = ∫ x, ∫ a, f (a, x) ∂torusVolume ∂torusVolume from
      integral_integral_swap hfi]
    have hinner (x : Torus) : (∫ a, f (a, x) ∂torusVolume) =
        torusVolume.real U * characteristic W x := by
      dsimp only [f]
      rw [integral_mul_const, integral_sub_left_eq_self, integral_characteristic hU.nullMeasurableSet]
      rfl
    simp_rw [hinner]
    rw [integral_const_mul, integral_characteristic hW.nullMeasurableSet]
    rfl
  have hIz (a : Torus) (ha : a ∉ Metric.ball 0 (2 * r)) : I a = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ W
    · by_cases hx' : x - a ∈ U
      · have hdist : ‖a‖ < 2 * r := by
          have hh := dist_triangle x c (x - a)
          have hxB : dist x c < r := (hWB hx)
          have hxB' : dist (x - a) c < r := (hUB hx')
          rw [dist_eq_norm, sub_sub_cancel] at hh
          rw [dist_comm c (x - a)] at hh
          linarith
        exact False.elim (ha (by simpa only [Metric.mem_ball, dist_zero_right] using hdist))
      · simp [f, characteristic, hx']
    · simp [f, characteristic, hx]
  let P := ∫ x in Metric.ball c (4 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)
  have hPn : 0 ≤ P := integral_nonneg fun _ ↦ norm_nonneg _
  have hIbound (a : Torus) (ha : a ∈ Metric.ball 0 (2 * r)) : I a ≤ 2 * r * P := by
    have han : ‖a‖ < 2 * r := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    by_cases hex : ∃ x : Torus, x ∈ W ∧ x - a ∈ U
    · obtain ⟨x₀, hx₀, hx₀'⟩ := hex
      have horder : 0 ≤ ⟪n, shortestLift a⟫ := by
        simpa only [sub_sub_cancel] using hordered (x₀ - a) hx₀' x₀ hx₀
      let g : Torus → ℝ := orderDefect E a
      have hgm : Measurable g := measurable_orderDefect hE a
      have hgb (x : Torus) : ‖g x‖ ≤ 1 := orderDefect_bound E a x
      have hgi : Integrable g torusVolume :=
        Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
      have hminor (x : Torus) : f (a, x) ≤ B.indicator g x := by
        by_cases hx : x ∈ W
        · by_cases hx' : x - a ∈ U
          · have hxE : x ∈ E := hWE hx
            have hxE' : x - a ∉ E := hUE hx'
            simp [f, characteristic, hx, hx', g, B, hWB hx, hxE, hxE', orderDefect]
          · simp only [f, characteristic, indicator_of_notMem hx', zero_mul]
            exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
        · simp only [f, characteristic, indicator_of_notMem hx, mul_zero]
          exact indicator_nonneg (fun _ _ ↦ orderDefect_nonneg _ _ _) _
      have hleft : I a ≤ ∫ x in B, g x ∂torusVolume := by
        rw [← integral_indicator hB]
        apply integral_mono _ (hgi.indicator hB) hminor
        exact Integrable.of_bound (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (Eventually.of_forall fun x ↦ hfb (a, x))
      have htrans := characteristic_ordered_translation_bound hE hμ hN hpolar hn c (r := r) hr horder
      rw [norm_shortestLift, quotientMap_shortestLift] at htrans
      have hpmono : (∫ x in Metric.ball c (r + r + ‖a‖),
          ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤ P :=
        setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
          (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall fun _ hx ↦
            Metric.ball_subset_ball (by linarith : r + r + ‖a‖ ≤ 4 * r) hx)
      exact hleft.trans (htrans.trans ((mul_le_mul_of_nonneg_left hpmono (norm_nonneg a)).trans
        (mul_le_mul_of_nonneg_right han.le hPn)))
    · have heq : I a = 0 := by
        apply integral_eq_zero_of_ae
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ W
        · have hx' : x - a ∉ U := fun hx' ↦ hex ⟨x, hx, hx'⟩
          simp [f, characteristic, hx']
        · simp [f, characteristic, hx]
      rw [heq]
      positivity
  have hir : (∫ a, I a ∂torusVolume) = ∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    by_cases ha : a ∈ Metric.ball 0 (2 * r)
    · simp [ha]
    · simp [ha, hIz a ha]
  have hbound : (∫ a in Metric.ball 0 (2 * r), I a ∂torusVolume) ≤
      torusVolume.real (Metric.ball (0 : Torus) (2 * r)) * (2 * r * P) := by
    calc
      _ ≤ ∫ _ in Metric.ball 0 (2 * r), (2 * r * P) ∂torusVolume :=
        setIntegral_mono_on hIi.integrableOn (integrable_const _)
          Metric.isOpen_ball.measurableSet hIbound
      _ = _ := by simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hvol : torusVolume.real (Metric.ball (0 : Torus) (2 * r)) ≤ 64 * r ^ 3 := by
    rw [Measure.real_def, volume_torusBall 0 (by positivity) (by linarith),
      ENNReal.toReal_ofReal (by positivity)]
    nlinarith [Real.pi_lt_four, pow_pos hr 3]
  rw [← hIeq, hir]
  exact hbound.trans ((mul_le_mul_of_nonneg_right hvol (by positivity)).trans (by
    dsimp [P]
    ring_nf
    exact le_rfl))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

lemma shortestLift_eq_of_lift {a : Torus} {v : Cover} (hv : quotientMap v = a)
    (hn : ‖v‖ < 1 / 2) : shortestLift a = v := by rw [← hv, shortestLift_quotientMap hn]

lemma inner_shortestLift_sub_nonneg {c y x z : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r t : ℝ} (hyr : dist y c < r) (hxr : dist x c < t) (hzr : dist z y < t)
    (hsmall : r + 2 * t ≤ 1 / 2) (hheight : 2 * t ≤ ⟪n, shortestLift (y - c)⟫) :
    0 ≤ ⟪n, shortestLift (z - x)⟫ := by
  have he : shortestLift (z - x) = shortestLift (y - c) + shortestLift (z - y) -
      shortestLift (x - c) := by
    apply shortestLift_eq_of_lift
    · simp only [quotientMap_sub, quotientMap_add, quotientMap_shortestLift]; abel
    · have hh := (norm_sub_le (shortestLift (y - c) + shortestLift (z - y))
        (shortestLift (x - c))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      have hy' : ‖shortestLift (y - c)‖ < r := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hyr
      have hz' : ‖shortestLift (z - y)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hzr
      have hx' : ‖shortestLift (x - c)‖ < t := by
        simpa only [norm_shortestLift, ← dist_eq_norm] using hxr
      linarith
  rw [he, inner_sub_right, inner_add_right]
  have hx := abs_real_inner_le_norm n (shortestLift (x - c))
  have hz := abs_real_inner_le_norm n (shortestLift (z - y))
  simp only [hn, one_mul, norm_shortestLift, ← dist_eq_norm, abs_le] at hx hz
  linarith [hx.2, hz.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ordered_density_normal_oscillation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {c a b : Torus} {n : Cover} (hnorm : ‖n‖ = 1)
    {r t δ : ℝ} (hr : 0 < r) (hsmall : r ≤ 1 / 16) (ht : 0 < t) (htr : t ≤ r)
    (hδ : 0 < δ) (ha : dist a c < r) (hb : dist b c < r)
    (hda : δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    (hdb : δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball b t))
    (hheight : 2 * t ≤ ⟪n, shortestLift (b - a)⟫) :
    δ ^ 2 * (t / r) ^ 6 ≤ 131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r) := by
  have hba : dist b a < 2 * r := by linarith [dist_triangle b c a, dist_comm c a]
  have hUB : Eᶜ ∩ Metric.ball a t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x a < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x a c]
  have hWB : E ∩ Metric.ball b t ⊆ Metric.ball c (2 * r) := by
    intro x hx
    have hh : dist x b < t := hx.2
    exact show dist x c < 2 * r from by linarith [dist_triangle x b c]
  have hsep : ∀ x ∈ Eᶜ ∩ Metric.ball a t, ∀ z ∈ E ∩ Metric.ball b t,
      0 ≤ ⟪n, shortestLift (z - x)⟫ := by
    intro x hx z hz
    exact inner_shortestLift_sub_nonneg hnorm hba hx.2 hz.2 (by linarith) hheight
  have hp := ordered_volume_product_bound hE hμ hN hpolar hn
    (hE.compl.inter Metric.isOpen_ball.measurableSet) (hE.inter Metric.isOpen_ball.measurableSet)
    inter_subset_left inter_subset_left c (by positivity : 0 < 2 * r) (by linarith) hUB hWB n hsep
  have hprod := mul_le_mul hda hdb (by positivity : 0 ≤ δ * t ^ 3) ENNReal.toReal_nonneg
  have hm : (∫ x in Metric.ball c (4 * (2 * r)),
      ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in Metric.closedBall c (8 * r), ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := by
    rw [show 4 * (2 * r) = 8 * r by ring]
    exact setIntegral_mono_set (integrable_norm_sub_normal hN hn n).integrableOn
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Eventually.of_forall fun _ hx ↦ Metric.ball_subset_closedBall hx)
  have hh := hprod.trans (hp.trans (mul_le_mul_of_nonneg_left hm (by positivity)))
  apply (mul_le_mul_iff_left₀ (pow_pos hr 6)).mp
  calc
    δ ^ 2 * (t / r) ^ 6 * r ^ 6 = (δ * t ^ 3) * (δ * t ^ 3) := by field_simp
    _ ≤ 128 * (2 * r) ^ 4 * ∫ x in Metric.closedBall c (8 * r),
        ‖N x - n‖ ∂(spatialNormalMeasure μ : Measure Torus) := hh
    _ = (131072 * normalOscillation (spatialNormalMeasure μ) N c n (8 * r)) * r ^ 6 := by
      rw [normalOscillation]
      field_simp
      ring

lemma normal_oscillation_implies_boundary_flatness {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ R →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {c : Torus} (hc : c ∈ B) {n : Cover} (hnorm : ‖n‖ = 1)
    (hlim : Tendsto (normalOscillation (spatialNormalMeasure μ) N c n) (𝓝[>] 0) (𝓝 0)) :
    BoundaryFlatAt B c n := by
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  have hthreshold : 0 < δ ^ 2 * (η / 4) ^ 6 := by positivity
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      131072 * normalOscillation (spatialNormalMeasure μ) N c n s < δ ^ 2 * (η / 4) ^ 6 :=
    (show Tendsto (fun s ↦ 131072 * normalOscillation (spatialNormalMeasure μ) N c n s)
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero] using hlim.const_mul 131072).eventually
        (Iio_mem_nhds hthreshold)
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hR (by norm_num : (0 : ℝ) < 1 / 16))),
      eventually_nhdsGT_zero_mul_left (by norm_num : (0 : ℝ) < 8) hevent] with r hr hrsmall hos
  have hrpos : 0 < r := hr
  have hrR : r ≤ R := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_left _ _)
  have hr16 : r ≤ 1 / 16 := (show r < min R (1 / 16) from hrsmall).le.trans (min_le_right _ _)
  let t := η * r / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htr : t ≤ r := by dsimp [t]; nlinarith
  have htR : t ≤ R := htr.trans hrR
  have hquot : t / r = η / 4 := by dsimp [t]; field_simp
  have hforbid : ∀ a ∈ B, dist a c < r → ∀ b ∈ B, dist b c < r →
      ¬ 2 * t ≤ ⟪n, shortestLift (b - a)⟫ := by
    intro a ha har b hb hbr hh
    have hh' := ordered_density_normal_oscillation hE hμ hN hpolar hn hnorm hrpos hr16 ht htr
      hδ har hbr (hd a ha t ht htR).2 (hd b hb t ht htR).1 hh
    rw [hquot] at hh'
    exact (not_lt_of_ge hh') hos
  intro y hy hyr
  have hcc : dist c c < r := by simpa only [dist_self] using hrpos
  have hl : ⟪n, shortestLift (y - c)⟫ < 2 * t := lt_of_not_ge (hforbid c hc hcc y hy hyr)
  have he : shortestLift (c - y) = -shortestLift (y - c) := by
    apply shortestLift_eq_of_lift
    · rw [quotientMap_neg, quotientMap_shortestLift]; abel
    · rw [norm_neg, norm_shortestLift, ← dist_eq_norm]
      linarith
  have hk := lt_of_not_ge (hforbid y hy hyr c hc hcc)
  rw [he, inner_neg_right] at hk
  have habs : |⟪n, shortestLift (y - c)⟫| < 2 * t := abs_lt.mpr ⟨by linarith, hl⟩
  apply habs.trans_le
  dsimp [t]
  nlinarith

theorem isMinimizerAt_boundary_flat_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      BoundaryFlatAt (frontier (openRepresentative E)) c (N c) := by
  obtain ⟨R, δ, hR, hδ, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  have hsupp := Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))
  have hflat := isMinimizerAt_normal_oscillation_ae hV hE hmin hμ hN hn
  filter_upwards [hsupp, hn, hflat] with c hc hnc hl
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact normal_oscillation_implies_boundary_flatness hE hμ hN hpolar hn hR hδ hd
    (spatialNormalMeasure_support_subset_boundary hE hμ hc) hnc hl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVLipschitzGraph
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma ediam_metricBall_le (a : Torus) {r : ℝ} (_hr : 0 ≤ r) :
    ediam (Metric.ball a r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hh := dist_triangle_right x y a
  exact hh.trans (by linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy])

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma hausdorff_two_le_open_of_lower_density (σ : FiniteMeasure Torus) (S U : Set Torus)
    (hU : IsOpen U) (hSU : S ⊆ U) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
  classical
  let r : ℕ → ℝ := fun n ↦ R / ((n : ℝ) + 1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrR (n) : r n ≤ R := by
    dsimp [r]
    exact div_le_self hR.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, mul_one_div] using hh
  have heps : ∀ a ∈ S, ∃ e : ℝ, 0 < e ∧ Metric.ball a e ⊆ U := by
    intro a ha
    exact Metric.isOpen_iff.mp hU a (hSU ha)
  choose e he heU using heps
  let rad (n : ℕ) (a : Torus) : ℝ := if ha : a ∈ S then min (r n) (e a ha) else r n
  have hrad (n : ℕ) (a : Torus) (ha : a ∈ S) : 0 < rad n a := by
    simp only [rad, dite_eq_left ha]
    exact lt_min (hr n) (he a ha)
  have hradle (n : ℕ) (a : Torus) : rad n a ≤ r n := by
    by_cases ha : a ∈ S
    · simp only [rad, dite_eq_left ha]; exact min_le_left _ _
    · simp only [rad, dite_eq_right ha]; exact le_rfl
  have hradU (n : ℕ) (a : Torus) (ha : a ∈ S) : Metric.ball a (rad n a) ⊆ U := by
    apply (Metric.ball_subset_ball ?_).trans (heU a ha)
    simp only [rad, dite_eq_left ha]
    exact min_le_right _ _
  have hex (n : ℕ) := Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id
    (rad n) (r n) (fun a _ ↦ hradle n a) 4 (by norm_num)
  choose u hu hdis hcov using hex
  have hcount (n) : (u n).Countable :=
    (hdis n).countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
      (fun a ha ↦ ⟨a, Metric.mem_ball_self (hrad n a (hu n ha))⟩)
  let : ∀ n, Countable (u n) := fun n ↦ (hcount n).to_subtype
  let t (n : ℕ) (a : u n) : Set Torus := Metric.ball (a : Torus) (4 * rad n a)
  have hdiam' (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * rad n a) := by
    simpa only [t, show (2 : ℝ) * (4 * rad n a) = 8 * rad n a by ring] using
      ediam_metricBall_le (a : Torus) (show 0 ≤ 4 * rad n a from by
        have hh := hrad n a (hu n a.property); positivity)
  have hdiam (n : ℕ) (a : u n) : ediam (t n a) ≤ ENNReal.ofReal (8 * r n) :=
    (hdiam' n a).trans (ENNReal.ofReal_le_ofReal (by nlinarith [hradle n a]))
  have hcover (n) : S ⊆ ⋃ a : u n, t n a := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov n a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hsub (Metric.mem_ball_self (hrad n a ha))⟩
  have hstep (n : ℕ) (a : u n) : ediam (t n a) ^ (2 : ℝ) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := by
    have hrpos := hrad n a (hu n a.property)
    have hlow := hl a (hu n a.property) (rad n a) hrpos ((hradle n a).trans (hrR n))
    have hb : ENNReal.ofReal (c * rad n a ^ 2) ≤
        (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hlow
    calc
      _ = ediam (t n a) ^ (2 : ℕ) := ENNReal.rpow_two _
      _ ≤ (ENNReal.ofReal (8 * rad n a)) ^ (2 : ℕ) := pow_le_pow_left' (hdiam' n a) _
      _ = ENNReal.ofReal (64 / c) * ENNReal.ofReal (c * rad n a ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ ≤ _ := mul_le_mul_right hb _
  have hsum (n : ℕ) : (∑' a : u n, ediam (t n a) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (64 / c) * (σ : Measure Torus) U := by
    calc
      _ ≤ ∑' a : u n, ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a)) := ENNReal.tsum_le_tsum (hstep n)
      _ = ENNReal.ofReal (64 / c) *
          (∑' a : u n, (σ : Measure Torus) (Metric.ball (a : Torus) (rad n a))) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (64 / c) *
          (σ : Measure Torus) (⋃ a ∈ u n, Metric.ball a (rad n a)) := by
        congr 1
        exact (measure_biUnion (hcount n) (hdis n)
          (fun _ _ ↦ Metric.isOpen_ball.measurableSet)).symm
      _ ≤ _ := mul_le_mul_right (measure_mono (by
        intro x hx
        obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
        exact hradU n a (hu n ha) hx)) _
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (8 * r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr0.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 S
    (fun n ↦ ENNReal.ofReal (8 * r n)) hlim t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

lemma hausdorff_two_le_measure_of_lower_density (σ : FiniteMeasure Torus) (S : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ S, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r)) :
    Measure.hausdorffMeasure 2 S ≤ ENNReal.ofReal (64 / c) * (σ : Measure Torus) S := by
  have h0 : ENNReal.ofReal (64 / c) ≠ 0 := by positivity
  rw [S.measure_eq_iInf_isOpen (σ : Measure Torus),
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro U
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hSU
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf fun hU ↦ hausdorff_two_le_open_of_lower_density σ S U hU hSU hR hc hl

lemma hausdorff_two_null_of_lower_density (σ : FiniteMeasure Torus) (B : Set Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {S : Set Torus} (hSB : S ⊆ B) (hS : (σ : Measure Torus) S = 0) :
    Measure.hausdorffMeasure 2 S = 0 := by
  have hh := hausdorff_two_le_measure_of_lower_density σ S hR hc
    (fun a ha ↦ hl a (hSB ha))
  rw [hS, mul_zero] at hh
  exact le_zero_iff.mp hh

theorem isMinimizerAt_boundary_area_absolutelyContinuous {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (Measure.hausdorffMeasure 2).restrict (frontier (openRepresentative E)) ≪
      (spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  intro S hS
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet]
  apply hausdorff_two_null_of_lower_density (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) hR hc (hl μ hμ)
  · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact inter_subset_right
  · exact measure_mono_null inter_subset_left hS

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_zero_of_nonzero_constant_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    (S : Set X) (L : X → X →L[ℝ] ℝ)
    (hL : ∀ x ∈ S, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) S x)
    (hne : ∀ x ∈ S, L x ≠ 0) : ν S = 0 := by
  classical
  have hex : ∀ x : S, ∃ v : X, L x v = 1 := by
    intro x
    have hh : ∃ w : X, L x w ≠ 0 := by
      by_contra! hh
      apply hne x x.property
      ext w
      exact hh w
    obtain ⟨w, hw⟩ := hh
    exact ⟨(L x w)⁻¹ • w, by simp [hw]⟩
  choose v hv using hex
  let A : X → X →L[ℝ] X := fun x ↦ if hx : x ∈ S then
    ContinuousLinearMap.id ℝ X - (L x).smulRight (v ⟨x, hx⟩) else 0
  have hA : ∀ x ∈ S, HasFDerivWithinAt (fun y : X ↦ y) (A x) S x := by
    intro x hx
    dsimp only [A]
    rw [dite_eq_left hx]
    convert (hasFDerivWithinAt_id x S).sub ((hL x hx).smul_const (v ⟨x, hx⟩)) using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    simp
  have hdet : ∀ x ∈ S, (A x).det = 0 := by
    intro x hx
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hker
    have hvne : v ⟨x, hx⟩ ≠ 0 := by
      intro hh
      have hh' := hv ⟨x, hx⟩
      rw [hh, map_zero] at hh'
      norm_num at hh'
    have hmem : v ⟨x, hx⟩ ∈ (A x).toLinearMap.ker := by
      change A x (v ⟨x, hx⟩) = 0
      have hvx := hv ⟨x, hx⟩
      change L x (v ⟨x, hx⟩) = 1 at hvx
      simp [A, hx, hvx]
    rw [hker] at hmem
    exact hvne hmem
  have hh := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero ν hA hdet
  simpa only [image_id'] using hh

lemma ae_constant_derivative_eq_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    (S : Set X) (L : X → X →L[ℝ] ℝ)
    (hL : ∀ x ∈ S, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) S x) :
    ∀ᵐ x ∂ν, x ∈ S → L x = 0 := by
  rw [ae_iff]
  have hh := volume_zero_of_nonzero_constant_derivative ν {x ∈ S | L x ≠ 0} L
    (fun x hx ↦ (hL x hx.1).mono (sep_subset _ _)) (fun _ hx ↦ hx.2)
  simpa only [Classical.not_imp] using hh

lemma normalGraph_lipschitz {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) : LipschitzWith (1 + K) (normalGraph n g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : normalGraph n g x - normalGraph n g y =
      normalPlaneEmbedding n (x - y) + (g x - g y) • n := by
    change normalPlaneLinearIsometry n x + g x • n -
      (normalPlaneLinearIsometry n y + g y • n) = _
    rw [show normalPlaneEmbedding n (x - y) =
      normalPlaneLinearIsometry n x - normalPlaneLinearIsometry n y from (normalPlaneLinearIsometry n).map_sub x y, sub_smul]
    abel
  have hh := norm_add_le (normalPlaneEmbedding n (x - y)) ((g x - g y) • n)
  rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one] at hh
  have hb := hg.norm_sub_le x y
  rw [dist_eq_norm, he, dist_eq_norm]
  change ‖normalPlaneEmbedding n (x - y) + (g x - g y) • n‖ ≤ (1 + (K : ℝ)) * ‖x - y‖
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVTriangleRegion
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma BoundaryFlatAt.exists_small_cone {B : Set Torus} {c : Torus} {n : Cover}
    (hf : BoundaryFlatAt B c n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ B, dist y c < R →
      |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c := by
  obtain ⟨R, hR, heR⟩ := Metric.mem_nhdsWithin_iff.mp (hf (ε / 2) (by positivity))
  refine ⟨R / 2, by positivity, ?_⟩
  intro y hy hyr
  by_cases hyc : y = c
  · subst y
    have hz : shortestLift (0 : Torus) = 0 := shortestLift_eq_of_lift rfl (by norm_num)
    simp [hz]
  · have hd : 0 < dist y c := dist_pos.mpr hyc
    have hh := heR ⟨(show dist (2 * dist y c) 0 < R by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith),
      (show 2 * dist y c ∈ Ioi (0 : ℝ) by change 0 < 2 * dist y c; positivity)⟩
    have hh' := hh y hy (by linarith)
    nlinarith

lemma BoundaryFlatAt.hasFDerivWithinAt_inner_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → Cover} {K : ℝ≥0} (hf : LipschitzWith K f)
    {B : Set Torus} {S : Set X} {a : Torus} {x : X} {n : Cover}
    (hS : ∀ y ∈ S, a + quotientMap (f y) ∈ B)
    (hflat : BoundaryFlatAt B (a + quotientMap (f x)) n) :
    HasFDerivWithinAt (fun y ↦ ⟪n, f y⟫) (0 : X →L[ℝ] ℝ) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨R, hR, hcone⟩ := hflat.exists_small_cone (div_pos hε hK)
  have hlocal : ∀ᶠ y in 𝓝 x, f y ∈ Metric.ball (f x) (min R (1 / 2)) :=
    hf.continuous.continuousAt.eventually (Metric.ball_mem_nhds _ (lt_min hR (by norm_num)))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlocal] with y hy hyl
  have hdist : dist (a + quotientMap (f y)) (a + quotientMap (f x)) ≤ dist (f y) (f x) := by
    rw [dist_add_left]
    rw [dist_eq_norm, ← quotientMap_sub, dist_eq_norm]
    exact norm_quotientMap_le (f y - f x)
  have hsub : a + quotientMap (f y) - (a + quotientMap (f x)) = quotientMap (f y - f x) := by
    rw [quotientMap_sub]
    abel
  have hsmall : ‖f y - f x‖ < 1 / 2 := by
    rw [← dist_eq_norm]
    exact (show dist (f y) (f x) < min R (1 / 2) from hyl).trans_le (min_le_right _ _)
  have hh := hcone (a + quotientMap (f y)) (hS y hy)
    (hdist.trans_lt ((show dist (f y) (f x) < min R (1 / 2) from hyl).trans_le (min_le_left _ _)))
  rw [hsub, shortestLift_quotientMap hsmall] at hh
  have hb := hf.dist_le_mul y x
  have hc := mul_le_mul_of_nonneg_left (hdist.trans hb) (le_of_lt (div_pos hε hK))
  simp only [zero_apply, sub_zero, ← inner_sub_right, Real.norm_eq_abs]
  rw [← dist_eq_norm]
  calc
    |⟪n, f y - f x⟫| ≤ ε / ((K : ℝ) + 1) * dist (a + quotientMap (f y))
      (a + quotientMap (f x)) := hh
    _ ≤ ε / ((K : ℝ) + 1) * ((K : ℝ) * dist y x) := hc
    _ ≤ ε * dist y x := by
      have hk : (K : ℝ) / ((K : ℝ) + 1) ≤ 1 := (div_le_one hK).mpr (by linarith)
      have hh' := mul_le_mul_of_nonneg_left hk (mul_nonneg hε.le (dist_nonneg : 0 ≤ dist y x))
      calc
        _ = ε * dist y x * ((K : ℝ) / ((K : ℝ) + 1)) := by ring
        _ ≤ ε * dist y x * 1 := hh'
        _ = _ := mul_one _

lemma lipschitz_boundary_parameter_tangent
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    {f : X → Cover} {K : ℝ≥0} (hf : LipschitzWith K f)
    {B : Set Torus} {S : Set X} {a : Torus} (N : X → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (f y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (f x)) (N x)) :
    ∀ᵐ x ∂ν, x ∈ S → (innerSL ℝ (N x)).comp (fderiv ℝ f x) = 0 := by
  let T := {x ∈ S | DifferentiableAt ℝ f x}
  let L : X → X →L[ℝ] ℝ := fun x ↦ (innerSL ℝ (N x)).comp (fderiv ℝ f x)
  have hL : ∀ x ∈ T, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) T x := by
    intro x hx
    have hd : HasFDerivWithinAt (fun y : X ↦ ⟪N x, f y⟫) (L x) T x :=
      ((innerSL ℝ (N x)).hasFDerivAt.comp x hx.2.hasFDerivAt).hasFDerivWithinAt
    have hz := (hflat x hx.1).hasFDerivWithinAt_inner_zero hf
      (fun y hy ↦ hS y hy.1) (S := T)
    convert hd.sub hz using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (funext y; simp) | simp [L]
  have hae := ae_constant_derivative_eq_zero ν T L hL
  filter_upwards [hae, hf.ae_differentiableAt (μ := ν)] with x hx hd
  exact fun hs ↦ hx ⟨hs, hd⟩

lemma normalGraph_tangent_ae {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : Set Torus} {S : Set Plane} {a : Torus} (N : Plane → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) (N x)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → ∀ v : Plane,
      ⟪N x, normalPlaneEmbedding n v + (fderiv ℝ g x v) • n⟫ = 0 := by
  have hh := lipschitz_boundary_parameter_tangent volume (normalGraph_lipschitz hn hg) N hS hflat
  filter_upwards [hh, hg.ae_differentiableAt (μ := (volume : Measure Plane))] with x hx hd hs v
  have he := congrArg (fun q : Plane →L[ℝ] ℝ ↦ q v) (hx hs)
  rw [(normalGraph_hasFDerivAt hd).fderiv] at he
  exact he

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_derivative_norm_le_tilt {n m : Cover} (hn : ‖n‖ = 1)
    (L : Plane →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (horth : ∀ v : Plane, ⟪m, normalPlaneEmbedding n v + L v • n⟫ = 0) :
    ‖L‖ ≤ 2 * ‖m - n‖ := by
  by_cases hlarge : 1 / 2 ≤ ‖m - n‖
  · linarith
  have hsmall : ‖m - n‖ < 1 / 2 := lt_of_not_ge hlarge
  have hc := abs_real_inner_le_norm (m - n) n
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hn] at hc
  norm_num at hc
  have hmn : 1 / 2 ≤ ⟪m, n⟫ := by
    have hh := (abs_le.mp hc).1
    linarith
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv := abs_real_inner_le_norm (m - n) (normalPlaneEmbedding n v)
  rw [inner_sub_left, normalPlaneEmbedding_inner hn, sub_zero,
    normalPlaneEmbedding_norm] at hv
  have he : L v * ⟪m, n⟫ = - ⟪m, normalPlaneEmbedding n v⟫ := by
    have hh := horth v
    rw [inner_add_right, inner_smul_right] at hh
    linarith
  have heabs := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ⟪m, n⟫), abs_neg] at heabs
  rw [Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left hmn (abs_nonneg (L v))
  nlinarith

lemma normalGraph_gradient_bound_ae {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (hK : K ≤ 1)
    {B : Set Torus} {S : Set Plane} {a : Torus} (N : Plane → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) (N x)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → ‖fderiv ℝ g x‖ ≤ 2 * ‖N x - n‖ := by
  filter_upwards [normalGraph_tangent_ae hn hg N hS hflat] with x hx hs
  apply graph_derivative_norm_le_tilt hn _ _ (hx hs)
  exact (norm_fderiv_le_of_lipschitz ℝ hg).trans (by exact_mod_cast hK)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_antilipschitz {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) :
    AntilipschitzWith 1 (normalGraph n g) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have he : normalGraph n g x - normalGraph n g y =
      normalPlaneEmbedding n (x - y) + (g x - g y) • n := by
    change normalPlaneLinearIsometry n x + g x • n -
      (normalPlaneLinearIsometry n y + g y • n) = _
    rw [show normalPlaneEmbedding n (x - y) =
      normalPlaneLinearIsometry n x - normalPlaneLinearIsometry n y from
        (normalPlaneLinearIsometry n).map_sub x y, sub_smul]
    abel
  rw [he]
  have horth : ⟪normalPlaneEmbedding n (x - y), (g x - g y) • n⟫ = 0 := by
    rw [inner_smul_right, real_inner_comm, normalPlaneEmbedding_inner hn, mul_zero]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [normalPlaneEmbedding_norm] at hs
  nlinarith [norm_nonneg (x - y), norm_nonneg (normalPlaneEmbedding n (x - y) + (g x - g y) • n),
    sq_nonneg ‖(g x - g y) • n‖]

lemma normalGraph_torus_antilipschitz {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) :
    AntilipschitzWith 1 (fun x : D ↦ a + quotientMap (normalGraph n g x)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_add_left]
  have hs : ‖normalGraph n g x - normalGraph n g y‖ < 1 / 2 :=
    (norm_sub_le _ _).trans_lt (by linarith [hD x x.property, hD y y.property])
  have he : dist (quotientMap (normalGraph n g x)) (quotientMap (normalGraph n g y)) =
      dist (normalGraph n g x) (normalGraph n g y) := by
    rw [dist_eq_norm, ← quotientMap_sub, ← norm_shortestLift, shortestLift_quotientMap hs,
      dist_eq_norm]
  rw [he]
  simpa using (normalGraph_antilipschitz hn g).le_mul_dist x y

lemma normalGraph_preimage_area_null {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    {T : Set Torus} (hT : Measure.hausdorffMeasure 2 T = 0) :
    (volume : Measure Plane) {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} = 0 := by
  let F : D → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hh := (normalGraph_torus_antilipschitz hn g a D hD).hausdorffMeasure_preimage_le
    (by norm_num : (0 : ℝ) ≤ 2) T
  have hnull : Measure.hausdorffMeasure 2 (F ⁻¹' T) = 0 := by
    apply le_zero_iff.mp
    simpa only [hT, mul_zero] using hh
  have himage := (isometry_subtype_coe : Isometry (Subtype.val : D → Plane)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (F ⁻¹' T)
  have hset : Subtype.val '' (F ⁻¹' T) = {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} := by
    ext x
    simp [F, and_comm]
  rw [hset, hnull] at himage
  exact (Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Plane)
    (Measure.hausdorffMeasure 2)) himage

lemma isMinimizerAt_ae_on_normalGraph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (a : Torus) (S : Set Plane)
    (hsmall : ∀ x ∈ S, ‖normalGraph n g x‖ < 1 / 4)
    (hS : ∀ x ∈ S, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E))
    {p : Torus → Prop} (hp : ∀ᵐ b ∂(spatialNormalMeasure μ : Measure Torus), p b) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → p (a + quotientMap (normalGraph n g x)) := by
  have hnull : (spatialNormalMeasure μ : Measure Torus) {b | ¬ p b} = 0 := ae_iff.mp hp
  have ha := isMinimizerAt_boundary_area_absolutelyContinuous hV hE hmin hμ hnull
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet] at ha
  have hpre := normalGraph_preimage_area_null hn g a S hsmall ha
  rw [ae_iff]
  apply measure_mono_null _ hpre
  intro x hx
  have hh : x ∈ S ∧ ¬ p (a + quotientMap (normalGraph n g x)) := Classical.not_imp.mp hx
  exact ⟨hh.1, hh.2, hS x hh.1⟩

theorem isMinimizerAt_normalGraph_gradient_bound {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hunit : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : K ≤ 1) (a : Torus) (S : Set Plane)
    (hsmall : ∀ x ∈ S, ‖normalGraph n g x‖ < 1 / 4)
    (hS : ∀ x ∈ S, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S →
      ‖fderiv ℝ g x‖ ≤ 2 * ‖N (a + quotientMap (normalGraph n g x)) - n‖ := by
  let T := {x ∈ S | BoundaryFlatAt (frontier (openRepresentative E))
    (a + quotientMap (normalGraph n g x)) (N (a + quotientMap (normalGraph n g x)))}
  have hflat := isMinimizerAt_ae_on_normalGraph hV hE hmin hμ hn g a S hsmall hS
    (isMinimizerAt_boundary_flat_ae hV hE hmin hμ hN hpolar hunit)
  have hgrad := normalGraph_gradient_bound_ae hn hg hK
    (fun x ↦ N (a + quotientMap (normalGraph n g x)))
    (S := T) (fun x hx ↦ hS x hx.1) (fun _ hx ↦ hx.2)
  filter_upwards [hflat, hgrad] with x hx hgx hs
  exact hgx ⟨hs, hx hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_preimage_volume_le {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    (T : Set Torus) :
    (volume : Measure Plane) {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} ≤
      (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 T := by
  let F : D → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hh := (normalGraph_torus_antilipschitz hn g a D hD).hausdorffMeasure_preimage_le
    (by norm_num : (0 : ℝ) ≤ 2) T
  have hh' : Measure.hausdorffMeasure 2 (F ⁻¹' T) ≤ Measure.hausdorffMeasure 2 T := by
    simpa using hh
  have himage := (isometry_subtype_coe : Isometry (Subtype.val : D → Plane)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (F ⁻¹' T)
  have hset : Subtype.val '' (F ⁻¹' T) = {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} := by
    ext x
    simp [F, and_comm]
  rw [hset] at himage
  rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure Plane) (Measure.hausdorffMeasure 2),
    Measure.smul_apply]
  change (planeAreaFactor : ℝ≥0∞) * _ ≤ _
  rw [himage]
  exact mul_le_mul_right hh' _

lemma normalGraph_map_volume_le_perimeter
    (σ : FiniteMeasure Torus) (B U : Set Torus) (_hU : MeasurableSet U)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (a : Torus) (D : Set Plane)
    (hsmall : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    (hD : ∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ B ∩ U) :
    Measure.map (fun x ↦ a + quotientMap (normalGraph n g x)) ((volume : Measure Plane).restrict D) ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) • (σ : Measure Torus).restrict U := by
  let F : Plane → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hF : Measurable F :=
    (continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hn hg).continuous)).measurable
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.map_apply hF hT, Measure.restrict_apply (hT.preimage hF),
    Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]
  have hset : F ⁻¹' T ∩ D = {x ∈ D | F x ∈ (T ∩ U) ∩ B} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, ⟨hx.1, (hD x hx.2).2⟩, (hD x hx.2).1⟩
    · intro hx
      exact ⟨hx.2.1.1, hx.1⟩
  rw [hset]
  have hh := normalGraph_preimage_volume_le hn g a D hsmall ((T ∩ U) ∩ B)
  have ha := hausdorff_two_le_measure_of_lower_density σ ((T ∩ U) ∩ B) hR hc
    (fun x hx ↦ hl x hx.2)
  calc
    _ ≤ (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 ((T ∩ U) ∩ B) := hh
    _ ≤ (planeAreaFactor : ℝ≥0∞) * (ENNReal.ofReal (64 / c) * (σ : Measure Torus) ((T ∩ U) ∩ B)) :=
      mul_le_mul_right ha _
    _ ≤ ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) * (σ : Measure Torus) (T ∩ U) := by
      rw [mul_assoc]
      exact mul_le_mul_right (mul_le_mul_right (measure_mono inter_subset_left) _) _

theorem isMinimizerAt_normalGraph_good_energy_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
        LipschitzWith K g → K ≤ 1 → ∀ (a : Torus) (D : Set Plane), MeasurableSet D →
        (∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) →
      ∀ U : Set Torus, MeasurableSet U →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ U) →
      (∫⁻ x in D, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂(volume : Measure Plane)) ≤
        C * ∫⁻ b in U, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂(spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C : ℝ≥0∞ := 4 * ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c))
  refine ⟨C, by dsimp [C]; finiteness, ?_⟩
  intro μ hμ N hN hp hn n hnorm g K hg hK a D hD hsmall hBD U hU hDU
  let F : Plane → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hF : Measurable F :=
    (continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hnorm hg).continuous)).measurable
  have hgrad := isMinimizerAt_normalGraph_gradient_bound hV hE hmin hμ hN hp hn hnorm hg hK a D hsmall hBD
  have hgrad' : ∀ᵐ x ∂(volume : Measure Plane).restrict D,
      ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ≤ 4 * ENNReal.ofReal (‖N (F x) - n‖ ^ 2) := by
    rw [ae_restrict_iff' hD]
    filter_upwards [hgrad] with x hx hxd
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hx hxd) 2
    have he : (2 * ‖N (F x) - n‖) ^ 2 = 4 * ‖N (F x) - n‖ ^ 2 := by ring
    rw [he] at hh
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hh
  have hmeasure := normalGraph_map_volume_le_perimeter (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) U hU hR hc (hl μ hμ) hnorm hg a D hsmall
    (fun x hx ↦ ⟨by rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]; exact hBD x hx, hDU x hx⟩)
  have hmeas : Measurable (fun b ↦ ENNReal.ofReal (‖N b - n‖ ^ 2)) :=
    ((hN.sub_const n).norm.pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ x in D, 4 * ENNReal.ofReal (‖N (F x) - n‖ ^ 2) := lintegral_mono_ae hgrad'
    _ = 4 * ∫⁻ x in D, ENNReal.ofReal (‖N (F x) - n‖ ^ 2) :=
      lintegral_const_mul _ (hmeas.comp hF)
    _ = 4 * ∫⁻ b, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂Measure.map F ((volume : Measure Plane).restrict D) := by
      rw [lintegral_map hmeas hF]
    _ ≤ 4 * ∫⁻ b, ENNReal.ofReal (‖N b - n‖ ^ 2)
        ∂(((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) •
          (spatialNormalMeasure μ : Measure Torus).restrict U) :=
      mul_le_mul_right (lintegral_mono' hmeasure (le_refl _)) _
    _ = _ := by simp only [lintegral_smul_measure, smul_eq_mul, C, mul_assoc]

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy_oai := @OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy_oai
