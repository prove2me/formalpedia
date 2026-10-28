-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:41:53.193689+00:00
-- url     : https://prove2.me/submissions/41800914-0712-4fb1-9b69-8cdb14011d09

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

theorem exists_bounded_competitor {V : ℝ} (hV : V ∈ Icc 0 1) :
    ∃ E : Set Torus, FinitePerimeter E ∧ torusVolume E = ENNReal.ofReal V ∧ perimeter E ≤ 2 :=
  ⟨stripe V, finitePerimeter_stripe hV, volume_stripe hV, perimeter_stripe_le hV⟩

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

lemma realVolume_closedBall_le (a : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 4) :
    torusVolume.real (Metric.closedBall a r) ≤ 64 * r ^ 3 := by
  calc
    _ ≤ torusVolume.real (Metric.ball a (2 * r)) :=
      measureReal_mono (Metric.closedBall_subset_ball (by linarith))
    _ = (2 * r) ^ 3 * (Real.pi * 4 / 3) := by
      rw [Measure.real_def, volume_torusBall a (by positivity) (by linarith),
        ENNReal.toReal_ofReal (by positivity)]
    _ ≤ _ := by nlinarith [Real.pi_lt_four, pow_pos hr 3]

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

lemma volumeSupport_ae_eq_of_density {E : Set Torus} (hE : MeasurableSet E)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hd : ∀ a ∈ volumeSupport E, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a r)) :
    volumeSupport E =ᵐ[torusVolume] E := by
  have hs : ∀ᵐ a ∂torusVolume, a ∈ E → a ∈ volumeSupport E :=
    (ae_restrict_iff' hE).1 Measure.support_mem_ae
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average torusVolume
    (integrable_characteristic hE).locallyIntegrable 1
  filter_upwards [hs, hdiff] with a has had
  apply propext
  refine ⟨fun ha ↦ ?_, has⟩
  by_contra hnot
  change a ∉ E at hnot
  have hchar : characteristic E a = 0 := by simp [characteristic, hnot]
  have ht : Tendsto (fun r : ℝ ↦ ⨍ x in Metric.closedBall a r, characteristic E x ∂torusVolume)
      (𝓝[>] 0) (𝓝 0) := by
    have hh := had (fun _ : ℝ ↦ a) id tendsto_id
      (show ∀ᶠ r : ℝ in 𝓝[>] 0, a ∈ Metric.closedBall a (1 * id r) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        change a ∈ Metric.closedBall a (1 * r)
        rw [one_mul]
        exact Metric.mem_closedBall_self (le_of_lt hr))
    rw [hchar] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hlower : ∀ᶠ r : ℝ in 𝓝[>] 0,
      c / 64 ≤ ⨍ x in Metric.closedBall a r, characteristic E x ∂torusVolume := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with r hr hrR hr4
    have hrpos : 0 < r := hr
    have hb := hd a ha r hrpos hrR.le
    have hmono : torusVolume.real (E ∩ Metric.ball a r) ≤
        torusVolume.real (E ∩ Metric.closedBall a r) :=
      measureReal_mono (inter_subset_inter_right E Metric.ball_subset_closedBall)
    have hpos : 0 < torusVolume.real (Metric.closedBall a r) :=
      (mul_pos hc (pow_pos hrpos 3)).trans_le
        (hb.trans (hmono.trans (measureReal_mono inter_subset_right)))
    rw [setAverage_eq, setIntegral_characteristic hE _ Metric.isClosed_closedBall.measurableSet,
      smul_eq_mul, ← div_eq_inv_mul]
    apply (le_div_iff₀ hpos).2
    have hh := mul_le_mul_of_nonneg_left (realVolume_closedBall_le a hrpos hr4.le)
      (show 0 ≤ c / 64 by positivity)
    nlinarith
  have hh := ge_of_tendsto ht hlower
  linarith

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

theorem isMinimizerAt_volume_frontier_eq_zero {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    torusVolume (frontier (openRepresentative E)) = 0 := by
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_volume_density hV hE hmin
  have hs := volumeSupport_ae_eq_of_density hE hR hc
    (fun a ha r hr hh ↦ hd a r hr hh ((mem_volumeSupport_iff E a).1 ha))
  have ho := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hae : frontier (openRepresentative E) =ᵐ[torusVolume] (∅ : Set Torus) := by
    rw [frontier, (isOpen_openRepresentative E).interior_eq,
      isMinimizerAt_closure_openRepresentative hV hE hmin]
    filter_upwards [hs, ho] with x hx hy
    change ((x ∈ volumeSupport E) ∧ x ∉ openRepresentative E) = False
    change (x ∈ volumeSupport E) = (x ∈ E) at hx
    change (x ∈ openRepresentative E) = (x ∈ E) at hy
    simp only [hx, hy, and_not_self]
  rw [measure_congr hae, measure_empty]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

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
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityField_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityField a r ε) :=
  (radialDensityWeight_contDiff a r ε).smul (contDiff_id.sub contDiff_const)

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

lemma radialDensityField_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityField a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have hzero := radialDensityWeight_zero hr hε (le_of_lt (by simpa only [Metric.mem_closedBall,
    dist_eq_norm, not_le] using hh))
  exact hx (by simp [radialDensityField, hzero])

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
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
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalPlaneEmbedding_coordinates {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v) = normalPlaneProjection n v := by
  have h := normalPlaneCoordinates_reconstruct hn v
  rw [normalPlaneProjection]
  exact eq_sub_iff_add_eq.mpr h

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

lemma continuous_tubeSplit : Continuous tubeSplit := by
  change Continuous (fun x : Cover ↦ (x 0, discProjection x))
  fun_prop

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
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

lemma admissible_latticePeriodize {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hb : ∀ x, ‖F x‖ ≤ 1) : AdmissibleField (latticePeriodize F) := by
  refine ⟨latticePeriodize_contDiff hF hc,latticePeriodize_periodic F,?_⟩
  intro x
  rw [← periodic_representative (latticePeriodize_periodic F) x,
    (latticePeriodize_eventuallyEq hc hs (fun i ↦
      ⟨(representative_mem_fundamentalCube _ i).1,(representative_mem_fundamentalCube _ i).2.le⟩)).eq_of_nhds]
  exact hb _

lemma radialDensityWeight_one_on_inner {a x : Cover} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) (hx : x ∈ Metric.closedBall a r) :
    radialDensityWeight a s (s^2-r^2) x = 1 := by
  have hn : ‖x-a‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by nlinarith : 0 < s^2-r^2)).mpr
  nlinarith [norm_nonneg (x-a)]

lemma radialDensityField_norm_le {a : Cover} {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (x : Cover) : ‖radialDensityField a s ε x‖ ≤ s := by
  by_cases hx : s ≤ ‖x-a‖
  · simp only [radialDensityField,radialDensityWeight_zero hs hε hx,zero_smul,norm_zero]
    exact hs
  · rw [radialDensityField,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (radialDensityWeight_le_one _ _ _ _)).trans
      (le_of_not_ge hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

lemma norm_axial_sub_center (x : Cover) :
    ‖axialProjection (x-cubeCenter)‖ = ‖discProjection x-discCenter‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_succ,axialProjection_zero,axialProjection_succ,norm_zero,
    zero_pow (by omega : 2 ≠ 0),zero_add,PiLp.sub_apply,discProjection_apply]
  rfl

lemma axial_sub_center_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ axialProjection (x-cubeCenter)) :=
  axialProjection.contDiff.comp (contDiff_id.sub contDiff_const)

lemma tubeCalibration_contDiff (b : ContDiffBump (1/2 : ℝ)) (r s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (tubeCalibration b r s) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ b (x 0)) :=
    b.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff)
  exact (hb.smul ((radialDensityField_contDiff 0 s (s^2-r^2)).comp
    axial_sub_center_contDiff)).const_smul _

lemma tubeCalibration_norm (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Cover) : ‖tubeCalibration b r s x‖ ≤ 1 := by
  have hs : 0 < s := hr.trans hrs
  have hε : 0 < s^2-r^2 := by nlinarith
  rw [tubeCalibration,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  calc
    _ ≤ s⁻¹ * ‖radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter))‖ :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) b.le_one) (inv_nonneg.mpr hs.le)
    _ ≤ s⁻¹*s := mul_le_mul_of_nonneg_left (radialDensityField_norm_le hs.le hε _) (inv_nonneg.mpr hs.le)
    _ = 1 := inv_mul_cancel₀ hs.ne'

lemma tubeCalibration_support (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    tsupport (tubeCalibration b r s) ⊆
      tubeSplit ⁻¹' (Metric.closedBall (1/2 : ℝ) b.rOut ×ˢ Metric.closedBall discCenter s) := by
  have hs : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  apply closure_minimal _ ((Metric.isClosed_closedBall.prod Metric.isClosed_closedBall).preimage continuous_tubeSplit)
  intro x hx
  have hb : b (x 0) ≠ 0 := fun hz ↦ hx (by simp [tubeCalibration,hz])
  have hf : radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter)) ≠ 0 :=
    fun hz ↦ hx (by simp only [tubeCalibration,hz,smul_zero])
  have hn := radialDensityField_tsupport hs hε (subset_tsupport _ hf)
  simp only [Metric.mem_closedBall,dist_zero_right] at hn
  refine ⟨Metric.ball_subset_closedBall (by rwa [← b.support_eq]),?_⟩
  simpa only [tubeSplit_apply,Metric.mem_closedBall,dist_eq_norm,norm_axial_sub_center] using hn

lemma tubeCalibration_compact (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) : HasCompactSupport (tubeCalibration b r s) := by
  have hc : IsCompact (tubeSplit.symm '' (Metric.closedBall (1/2 : ℝ) b.rOut ×ˢ Metric.closedBall discCenter s)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  intro x hx
  exact ⟨tubeSplit x,tubeCalibration_support b hr hrs hx,tubeSplit.symm_apply_apply x⟩

lemma tubeCalibration_interior (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    tsupport (tubeCalibration b r s) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hm := tubeCalibration_support b hr hrs hx
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hh : |x 0-1/2| ≤ b.rOut := by simpa only [Metric.mem_closedBall,Real.dist_eq,tubeSplit_apply] using hm.1
    rw [abs_le] at hh
    constructor <;> linarith
  · have hn : ‖discProjection x-discCenter‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm,tubeSplit_apply] using hm.2
    have hh := (PiLp.norm_apply_le (discProjection x-discCenter) j).trans hn
    change |x j.succ-1/2| ≤ s at hh
    rw [abs_le] at hh
    constructor <;> linarith

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

lemma divergence_axial_sub_center (x : Cover) :
    divergence (fun y : Cover ↦ axialProjection (y-cubeCenter)) x = 2 := by
  have hf := axialProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const cubeCenter)
  change HasFDerivAt (fun y : Cover ↦ axialProjection (y-cubeCenter)) axialProjection x at hf
  simp only [divergence,hf.fderiv]
  simp only [Fin.sum_univ_succ,axialProjection_zero,axialProjection_succ]
  norm_num [PiLp.single_apply]

lemma gradient_axialScalar_pair (b : ContDiffBump (1/2 : ℝ)) (x : Cover) :
    ⟪gradient (fun y : Cover ↦ b (y 0)) x,axialProjection (x-cubeCenter)⟫ = 0 := by
  rw [inner_gradient_left]
  change fderiv ℝ ((b : ℝ → ℝ) ∘ (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ)) x _ = _
  rw [fderiv_comp x ((b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b).differentiable (by simp) (x 0))
    (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).differentiableAt]
  simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
  change (fderiv ℝ (b : ℝ → ℝ) (x 0)) (axialProjection (x-cubeCenter) 0) = 0
  rw [axialProjection_zero,map_zero]

lemma tubeCalibration_divergence_inner (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Cover) (hx : x ∈ coverTube r) :
    divergence (tubeCalibration b r s) x = (2/s)*b (x 0) := by
  have hn : ‖axialProjection (x-cubeCenter)‖ < r := by
    rw [norm_axial_sub_center]
    simpa only [Metric.mem_ball,dist_eq_norm,tubeSplit_apply] using hx.2
  have he : tubeCalibration b r s =ᶠ[𝓝 x]
      (fun y : Cover ↦ s⁻¹ • (b (y 0) • axialProjection (y-cubeCenter))) := by
    have hc := axial_sub_center_contDiff.continuous.norm
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hn)] with y hy
    rw [tubeCalibration,radialDensityField,
      radialDensityWeight_one_on_inner hr.le hrs (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy.le),
      one_smul,sub_zero]
  have hbd : Differentiable ℝ (fun y : Cover ↦ b (y 0)) :=
    ((b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b).comp (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).contDiff).differentiable (by simp)
  simp only [divergence,he.fderiv_eq]
  change divergence (fun y : Cover ↦ s⁻¹ • (b (y 0) • axialProjection (y-cubeCenter))) x = _
  have hf : DifferentiableAt ℝ (fun y : Cover ↦ b (y 0) • axialProjection (y-cubeCenter)) x :=
    (hbd x).smul (axial_sub_center_contDiff.differentiable (by simp) x)
  rw [divergence_const_smul hf (s⁻¹),
    divergence_smul_function (hbd x) (axial_sub_center_contDiff.differentiable (by simp) x),
    divergence_axial_sub_center,gradient_axialScalar_pair]
  ring

lemma tubeCalibration_periodic_divergence (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) (x : Cover) (hx : x ∈ coverTube r) :
    divergence (latticePeriodize (tubeCalibration b r s)) x = (2/s)*b (x 0) := by
  have hm := coverTube_subset_cube (hrs.le.trans hs.le) hx
  have he := latticePeriodize_eventuallyEq (tubeCalibration_compact b hr hrs)
    (tubeCalibration_interior b hb hr hrs hs) (fun i ↦ ⟨(hm i).1,(hm i).2.le⟩)
  simp only [divergence,he.fderiv_eq]
  exact tubeCalibration_divergence_inner b hr hrs x hx

lemma integral_axialScalar_coverTube {f : ℝ → ℝ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in coverTube r, f (x 0)) = (∫ t in Ico (0 : ℝ) 1, f t)*(Real.pi*r^2) := by
  let g : ℝ × Plane → ℝ := fun p ↦ f p.1
  have hint : IntegrableOn (fun x : Cover ↦ f (x 0)) (coverTube r) :=
    (((hf.comp (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).continuous).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r))).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g,Function.comp_def,tubeSplit_apply,coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  change (∫ x in coverTube r, f (x 0)) = _ at he
  rw [he,Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hi
  rw [integral_prod g hi]
  simp only [g,integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,
    EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal Real.pi_pos.le,
    integral_const_mul]
  ring

lemma tube_calibration_flux_le (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal ((2/s)*((∫ t in Ico (0 : ℝ) 1, b t)*(Real.pi*r^2))) ≤ perimeter (cubeTube r) := by
  have hp := admissible_latticePeriodize (tubeCalibration_contDiff b r s)
    (tubeCalibration_compact b hr hrs) (tubeCalibration_interior b hb hr hrs hs) (tubeCalibration_norm b hr hrs)
  have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' cubeTube r,
      divergence (latticePeriodize (tubeCalibration b r s)) x) ≤ perimeter (cubeTube r) :=
    le_iSup_of_le _ (le_iSup_of_le hp le_rfl)
  rw [cubeTube_lift (hrs.le.trans hs.le)] at hh
  rwa [setIntegral_congr_fun (measurableSet_coverTube r) (tubeCalibration_periodic_divergence b hb hr hrs hs),
    integral_const_mul,integral_axialScalar_coverTube b.continuous hr.le] at hh

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

lemma axialExhaustionBump_outer {a : ℝ} (ha : 0 < a) (ha' : a < 1/2) :
    (axialExhaustionBump a ha ha').rOut < 1/2 := by
  change (a+1/2)/2 < 1/2
  linarith

lemma axialExhaustionBump_integral {a : ℝ} (ha : 0 < a) (ha' : a < 1/2) :
    2*a ≤ ∫ t in Ico (0 : ℝ) 1, axialExhaustionBump a ha ha' t := by
  let b := axialExhaustionBump a ha ha'
  have hi : IntegrableOn (b : ℝ → ℝ) (Ico 0 1) :=
    (b.continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have hsub : Metric.closedBall (1/2 : ℝ) a ⊆ Ico 0 1 := by
    intro t ht
    have hh : |t-1/2| ≤ a := by simpa only [Metric.mem_closedBall,Real.dist_eq] using ht
    rw [abs_le] at hh
    constructor <;> linarith
  have hlo := setIntegral_mono_set hi (Eventually.of_forall fun _ ↦ b.nonneg)
    (Eventually.of_forall hsub)
  have he : (∫ t in Metric.closedBall (1/2 : ℝ) a, b t) = 2*a := by
    have hpoint (t : ℝ) (ht : t ∈ Metric.closedBall (1/2 : ℝ) a) : b t = 1 :=
      b.one_of_mem_closedBall ht
    rw [setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet hpoint,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,
      Real.volume_closedBall,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*a)]
  exact he ▸ hlo

lemma tube_calibration_lower_fixed_radius {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal ((2/s)*(Real.pi*r^2)) ≤ perimeter (cubeTube r) := by
  have hlim : Tendsto (fun a : ℝ ↦ ENNReal.ofReal ((2/s)*((2*a)*(Real.pi*r^2))))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (ENNReal.ofReal ((2/s)*(Real.pi*r^2)))) := by
    have hc : Continuous (fun a : ℝ ↦ (2/s)*((2*a)*(Real.pi*r^2))) := by fun_prop
    have hl := (ENNReal.continuous_ofReal.comp hc).tendsto (1/2 : ℝ)
    norm_num only [Function.comp_apply,mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),one_mul] at hl
    exact hl.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with a ha' ha
  have hb := tube_calibration_flux_le (axialExhaustionBump a ha ha')
    (axialExhaustionBump_outer ha ha') hr hrs hs
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hb
  have hs0 : 0 < s := hr.trans hrs
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (axialExhaustionBump_integral ha ha') (by positivity)) (by positivity)

theorem perimeter_cubeTube_eq {r : ℝ} (hr : 0 < r) (hs : r < 1/2) :
    perimeter (cubeTube r) = ENNReal.ofReal (2*Real.pi*r) := by
  apply le_antisymm (perimeter_cubeTube_le hr hs.le)
  have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal ((2/s)*(Real.pi*r^2)))
      (𝓝[>] r) (𝓝 (ENNReal.ofReal (2*Real.pi*r))) := by
    have hc : ContinuousAt (fun s : ℝ ↦ (2/s)*(Real.pi*r^2)) r :=
      (continuousAt_const.div continuousAt_id hr.ne').mul continuousAt_const
    have he : (2/r)*(Real.pi*r^2) = 2*Real.pi*r := by field_simp
    have hl := (ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto
    change Tendsto _ (𝓝 r) (𝓝 (ENNReal.ofReal ((2/r)*(Real.pi*r^2)))) at hl
    rw [he] at hl
    exact hl.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with s hrs hs
  exact tube_calibration_lower_fixed_radius hr hrs hs

end CubicTorus.UpperComparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
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

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Rigidity_LocalGraphSphere
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

lemma norm_quotientMap_eq_of_half_cube {z : Cover} (hz : ∀ i,|z i|≤1/2) :
    ‖quotientMap z‖=‖z‖ := by
  rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ‖(z i : AddCircle (1 : ℝ))‖^2=‖z i‖^2
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ)≠0)).mpr
    (by simpa using hz i),Real.norm_eq_abs]

lemma shortestLift_half_cube (x : Torus) (i : Fin 3) : |shortestLift x i|≤1/2 := by
  have h := UpperComparison.representative_mem_cube (x+quotientMap cubeCenter) i
  change |representative (x+quotientMap cubeCenter) i-(1/2)|≤1/2
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma preconnected_avoiding_frontier {X : Type*} [TopologicalSpace X]
    {U S : Set X} (hU : IsOpen U) (hS : IsPreconnected S) (havoid : Disjoint S (frontier U)) :
    S⊆U ∨ S⊆Uᶜ := by
  have hcov : S⊆U∪(closure U)ᶜ := by
    intro x hx
    by_cases hxu : x∈U
    · exact Or.inl hxu
    · right
      intro hxc
      exact disjoint_left.mp havoid hx (by rw [hU.frontier_eq]; exact ⟨hxc,hxu⟩)
  rcases hS.subset_or_subset hU isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hcov with h|h
  · exact Or.inl h
  · exact Or.inr (h.trans (compl_subset_compl.mpr subset_closure))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_MinimizerAxialCenter
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

lemma axialProjection_self {v : Cover} (hv : ‖v‖=1) : axialProjection v v=0 := by
  simp [hv]

lemma axialProjection_tangent {v x : Cover} (hx : ⟪v,x⟫=0) : axialProjection v x=x := by simp [hx]

lemma axialProjection_inner_zero {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    ⟪v,axialProjection v x⟫=0 := by
  rw [axialProjection_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv,one_pow,mul_one,sub_self]

lemma axialProjection_idempotent {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    axialProjection v (axialProjection v x)=axialProjection v x :=
  axialProjection_tangent (axialProjection_inner_zero hv x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isPreconnected_euclideanCylinder {v : Cover} (hv : ‖v‖=1) (c : Cover) (R : ℝ) :
    IsPreconnected (euclideanCylinder v c R) := by
  let P : Set (ℝ × Plane) := univ ×ˢ Metric.sphere 0 R
  let F : ℝ × Plane → Cover := fun p => c+p.1 • v+normalPlaneEmbedding v p.2
  have hP : IsPreconnected P := isPreconnected_univ.prod
    (isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Plane,finrank_euclideanSpace_fin]) 0 R)
  have hF : Continuous F := by
    exact (continuous_const.add (continuous_fst.smul continuous_const)).add
      ((normalPlaneLinearIsometry v).continuous.comp continuous_snd)
  have he : F '' P=euclideanCylinder v c R := by
    apply Subset.antisymm
    · rintro x ⟨⟨s,y⟩,hy,rfl⟩
      change ‖axialProjection v (c+s • v+normalPlaneEmbedding v y-c)‖=R
      rw [show c+s • v+normalPlaneEmbedding v y-c=s • v+normalPlaneEmbedding v y by abel,
        map_add,map_smul,axialProjection_self hv,smul_zero,zero_add,
        axialProjection_tangent (normalPlaneEmbedding_inner hv y),normalPlaneEmbedding_norm]
      simpa only [Metric.mem_sphere,dist_zero_right] using hy.2
    · intro x hx
      refine ⟨(⟪v,x-c⟫,normalPlaneCoordinates v (x-c)),⟨mem_univ _,?_⟩,?_⟩
      · simp only [Metric.mem_sphere,dist_zero_right]
        change ‖normalPlaneCoordinates v (x-c)‖=R
        rw [← normalPlaneEmbedding_norm v,normalPlaneEmbedding_coordinates hv]
        exact hx
      · change c+⟪v,x-c⟫ • v+normalPlaneEmbedding v (normalPlaneCoordinates v (x-c))=x
        have hh := normalPlaneCoordinates_reconstruct hv (x-c)
        calc
          _=c+(normalPlaneEmbedding v (normalPlaneCoordinates v (x-c))+⟪v,x-c⟫ • v) := by abel
          _=x := by rw [hh,add_sub_cancel]
  rw [← he]
  exact hP.image F hF.continuousOn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateAxis_norm (i : Fin 3) : ‖(EuclideanSpace.single i 1 : Cover)‖=1 := by simp

lemma axialProjection_axis_apply (i : Fin 3) (x : Cover) (j : Fin 3) :
    axialProjection (EuclideanSpace.single i 1) x j=if j=i then 0 else x j := by
  simp only [axialProjection_apply,EuclideanSpace.inner_single_left,conj_trivial,one_mul,
    PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply]
  split_ifs with h
  · subst j; simp
  · simp

lemma fin_three_other_coordinates (i : Fin 3) :
    ∃ j k : Fin 3,j≠i ∧ k≠i ∧ j≠k := by
  fin_cases i
  · exact ⟨1,2,by decide,by decide,by decide⟩
  · exact ⟨0,2,by decide,by decide,by decide⟩
  · exact ⟨0,1,by decide,by decide,by decide⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_TorusCylinders
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma torusAxialProjection_continuous (i : Fin 3) : Continuous (torusAxialProjection i) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).comp
  apply continuous_pi
  intro j
  by_cases h : j=i
  · simp only [h,ite_true]; exact continuous_const
  · simp only [ite_eq_right h]; exact PiLp.continuous_apply 2 (fun _ : Fin 3 => AddCircle (1 : ℝ)) j

lemma quotientMap_axialProjection (i : Fin 3) (x : Cover) :
    quotientMap (axialProjection (EuclideanSpace.single i 1) x)=torusAxialProjection i (quotientMap x) := by
  ext j
  simp only [quotientMap,PiLp.toLp_apply,axialProjection_axis_apply,torusAxialProjection_apply]
  split_ifs <;> simp

lemma norm_transverse_shortestLift (i : Fin 3) (x : Torus) :
    ‖axialProjection (EuclideanSpace.single i 1) (shortestLift x)‖=‖torusAxialProjection i x‖ := by
  have hh : ‖quotientMap (axialProjection (EuclideanSpace.single i 1) (shortestLift x))‖=
      ‖axialProjection (EuclideanSpace.single i 1) (shortestLift x)‖ := by
    apply norm_quotientMap_eq_of_half_cube
    intro j
    rw [axialProjection_axis_apply]
    split_ifs
    · norm_num
    · exact shortestLift_half_cube x j
  rw [quotientMap_axialProjection,quotientMap_shortestLift] at hh
  exact hh.symm

lemma quotientMap_image_small_cylinder (i : Fin 3) (c : Cover) {r : ℝ} (hr : r≤1/2) :
    quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r=
      {x : Torus | ‖torusAxialProjection i (x-quotientMap c)‖=r} := by
  apply Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    change ‖axialProjection (EuclideanSpace.single i 1) (z-c)‖=r at hz
    change ‖torusAxialProjection i (quotientMap z-quotientMap c)‖=r
    rw [← quotientMap_sub,← quotientMap_axialProjection,
      norm_quotientMap_eq_of_half_cube (fun j => by
        have h := PiLp.norm_apply_le (axialProjection (EuclideanSpace.single i 1) (z-c)) j
        rw [hz] at h
        exact h.trans hr),hz]
  · intro x hx
    refine ⟨c+shortestLift (x-quotientMap c),?_,?_⟩
    · change ‖axialProjection (EuclideanSpace.single i 1) (c+shortestLift (x-quotientMap c)-c)‖=r
      rw [add_sub_cancel_left,norm_transverse_shortestLift]
      exact hx
    · rw [quotientMap_add,quotientMap_shortestLift,add_sub_cancel]

lemma isOpen_axialTube (i : Fin 3) (c : Torus) (r : ℝ) : IsOpen (axialTube i c r) :=
  isOpen_lt (((torusAxialProjection_continuous i).comp (continuous_id.sub continuous_const)).norm) continuous_const

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialTube_zero_preconnected (i : Fin 3) (r : ℝ) : IsPreconnected (axialTube i 0 r) := by
  let P := axialProjection (EuclideanSpace.single i 1)
  let S : Set Cover := P ⁻¹' Metric.ball 0 r
  have hS : Convex ℝ S := (convex_ball (0 : Cover) r).linear_preimage P.toLinearMap
  have him : quotientMap '' S=axialTube i 0 r := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      change dist (P z) 0 < r at hz
      rw [dist_zero_right] at hz
      change ‖torusAxialProjection i (quotientMap z-0)‖ < r
      rw [sub_zero,← quotientMap_axialProjection]
      exact (norm_quotientMap_le (P z)).trans_lt hz
    · intro x hx
      refine ⟨shortestLift x,?_,quotientMap_shortestLift x⟩
      change dist (P (shortestLift x)) 0 < r
      rw [dist_zero_right,norm_transverse_shortestLift]
      simpa only [axialTube,mem_ofPred_eq,sub_zero] using hx
  rw [← him]
  exact hS.isPreconnected.image _ continuous_quotientMap.continuousOn

lemma axialTubeExterior_zero_preconnected (i : Fin 3) {r : ℝ} (hr0 : 0 ≤ r) (hr : r<1/2) :
    IsPreconnected (axialTubeExterior i 0 r) := by
  let v : Cover := EuclideanSpace.single i 1
  have hv : ‖v‖=1 := coordinateAxis_norm i
  let P := axialProjection v
  let S := euclideanCylinder v 0 (1/2)
  let T : Set Torus := quotientMap '' S
  have hS : IsPreconnected S := isPreconnected_euclideanCylinder hv 0 (1/2)
  have hT : IsPreconnected T := hS.image _ continuous_quotientMap.continuousOn
  have hTS : T⊆axialTubeExterior i 0 r := by
    intro x hx
    have hh := (quotientMap_image_small_cylinder i 0 (by norm_num : (1/2 : ℝ)≤1/2)).subset hx
    change ‖torusAxialProjection i (x-quotientMap 0)‖=1/2 at hh
    change r<‖torusAxialProjection i (x-0)‖
    have hq : quotientMap 0=(0 : Torus) := rfl
    rw [hq] at hh
    rw [hh]
    exact hr
  obtain ⟨j,k,hji,hki,hjk⟩ := fin_three_other_coordinates i
  let z₀ : Cover := (1/2 : ℝ) • EuclideanSpace.single j 1
  have hiz : ⟪v,z₀⟫=0 := by
    simp [v,z₀,EuclideanSpace.inner_single_left,Ne.symm hji]
  have hz₀ : z₀∈S := by
    change ‖P (z₀-0)‖=1/2
    rw [sub_zero,axialProjection_tangent hiz]
    simp [z₀,norm_smul]
  apply isPreconnected_of_forall (quotientMap z₀)
  intro x hx
  have hx' : r<‖torusAxialProjection i x‖ := by simpa only [axialTubeExterior,mem_ofPred_eq,sub_zero] using hx
  let z := shortestLift x
  let p := P z
  have hn : ‖p‖=‖torusAxialProjection i x‖ := norm_transverse_shortestLift i x
  have hp0 : 0<‖p‖ := hr0.trans_lt (hx'.trans_eq hn.symm)
  let k : ℝ := (1/2)/‖p‖
  let w := z+(k-1) • p
  have hk : 0<k := div_pos (by norm_num) hp0
  have hwp : P w=k • p := by
    change P (z+(k-1) • P z)=k • P z
    rw [map_add,map_smul,axialProjection_idempotent hv]
    module
  have hw : ‖P w‖=1/2 := by
    rw [hwp,norm_smul,Real.norm_of_nonneg hk.le]
    dsimp [k]; field_simp
  have hwS : w∈S := by change ‖P (w-0)‖=1/2; rwa [sub_zero]
  let f : ℝ → Torus := fun t => quotientMap (z+(((1-t)+t*k)-1) • p)
  have hf : Continuous f := continuous_quotientMap.comp
    (continuous_const.add (((continuous_const.sub continuous_id |>.add (continuous_id.mul continuous_const)).sub continuous_const).smul continuous_const))
  have hf0 : f 0=x := by simp [f,z,quotientMap_shortestLift]
  have hf1 : f 1=quotientMap w := by simp [f,w]
  have hpt (t : ℝ) : P (z+(((1-t)+t*k)-1) • p)=((1-t)+t*k) • p := by
    change P (z+(((1-t)+t*k)-1) • P z)=((1-t)+t*k) • P z
    rw [map_add,map_smul,axialProjection_idempotent hv]
    module
  have hfS : f '' Icc 0 1⊆axialTubeExterior i 0 r := by
    rintro y ⟨t,ht,rfl⟩
    have ht0 : 0≤1-t := sub_nonneg.mpr ht.2
    have ha : 0≤(1-t)+t*k := add_nonneg ht0 (mul_nonneg ht.1 hk.le)
    have hc : ∀ j,|(((1-t)+t*k) • p) j|≤1/2 := by
      intro j
      have hpj : |p j|≤1/2 := by
        change |axialProjection (EuclideanSpace.single i 1) (shortestLift x) j|≤1/2
        rw [axialProjection_axis_apply]
        split_ifs
        · norm_num
        · exact shortestLift_half_cube x j
      have hwj : |(P w) j|≤1/2 := by simpa only [Real.norm_eq_abs,hw] using PiLp.norm_apply_le (P w) j
      have he : (((1-t)+t*k) • p) j=(1-t)*p j+t*(P w) j := by
        rw [hwp]; simp only [PiLp.smul_apply,smul_eq_mul]; ring
      rw [he]
      calc
        _≤|(1-t)*p j|+|t*(P w) j| := abs_add_le _ _
        _=(1-t)*|p j|+t*|(P w) j| := by rw [abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg ht.1]
        _≤(1-t)*(1/2)+t*(1/2) := add_le_add (mul_le_mul_of_nonneg_left hpj ht0) (mul_le_mul_of_nonneg_left hwj ht.1)
        _=1/2 := by ring
    change r<‖torusAxialProjection i (quotientMap (z+(((1-t)+t*k)-1) • p)-0)‖
    rw [sub_zero,← quotientMap_axialProjection,hpt,norm_quotientMap_eq_of_half_cube hc,norm_smul,Real.norm_of_nonneg ha]
    have hkp : k*‖p‖=1/2 := by dsimp [k]; field_simp
    have hxp : r<‖p‖ := hx'.trans_eq hn.symm
    have hh : 0<(1-t)*(‖p‖-r)+t*((1/2)-r) := by
      by_cases ht1 : t=1
      · simpa only [ht1,sub_self,zero_mul,one_mul,zero_add] using sub_pos.mpr hr
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) (sub_pos.mpr hxp))
          (mul_nonneg ht.1 (sub_nonneg.mpr hr.le))
    nlinarith
  refine ⟨T∪f '' Icc 0 1,union_subset hTS hfS,Or.inl ⟨z₀,hz₀,rfl⟩,
    Or.inr ⟨0,by norm_num,hf0⟩,?_⟩
  exact hT.union (quotientMap w) ⟨w,hwS,rfl⟩ ⟨1,by norm_num,hf1⟩
    (isPreconnected_Icc.image _ hf.continuousOn)

lemma axialTube_preconnected (i : Fin 3) (c : Torus) (r : ℝ) :
    IsPreconnected (axialTube i c r) := by
  have he : axialTube i c r=(fun x : Torus => x-c) ⁻¹' axialTube i 0 r := by
    ext x; simp only [axialTube,mem_preimage,mem_ofPred_eq,sub_zero]
  rw [he]
  simpa only [Homeomorph.coe_addRight,sub_eq_add_neg] using (Homeomorph.addRight (-c)).isPreconnected_preimage.mpr (axialTube_zero_preconnected i r)

lemma axialTubeExterior_preconnected (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0 ≤ r) (hr : r<1/2) :
    IsPreconnected (axialTubeExterior i c r) := by
  have he : axialTubeExterior i c r=(fun x : Torus => x-c) ⁻¹' axialTubeExterior i 0 r := by
    ext x; simp only [axialTubeExterior,mem_preimage,mem_ofPred_eq,sub_zero]
  rw [he]
  simpa only [Homeomorph.coe_addRight,sub_eq_add_neg] using (Homeomorph.addRight (-c)).isPreconnected_preimage.mpr (axialTubeExterior_zero_preconnected i hr0 hr)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_cylindrical_boundary_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0 < r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
    E =ᵐ[torusVolume] axialTube i (quotientMap c) r ∨
      E =ᵐ[torusVolume] (axialTube i (quotientMap c) r)ᶜ := by
  let U := openRepresentative E
  let a := quotientMap c
  let B := axialTube i a r
  let D := axialTubeExterior i a r
  have hbd' : frontier U={x : Torus | ‖torusAxialProjection i (x-a)‖=r} :=
    hbd.trans (quotientMap_image_small_cylinder i c hr.le)
  have hBa : Disjoint B (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_lt hx) hz
  have hDa : Disjoint D (frontier U) := by
    rw [hbd']; exact disjoint_left.mpr fun x hx hz ↦ (ne_of_gt hx) hz
  have hB := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (axialTube_preconnected i a r) hBa
  have hD := preconnected_avoiding_frontier (isOpen_openRepresentative E)
    (axialTubeExterior_preconnected i a hr0.le hr) hDa
  have hnot : ∀ᵐ x ∂torusVolume,x∉frontier U := by
    rw [ae_iff]
    simp only [not_not]
    change torusVolume (frontier U)=0
    exact isMinimizerAt_volume_frontier_eq_zero hV hE hmin
  have hpart : ∀ᵐ x ∂torusVolume,x∈B ∨ x∈D := by
    filter_upwards [hnot] with x hx
    rw [hbd'] at hx
    exact lt_or_gt_of_ne hx
  have hEU := (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hne0 : ¬E =ᵐ[torusVolume] (∅ : Set Torus) := by
    intro h
    have hz := measure_congr h
    rw [measure_empty,hmin.2.1] at hz
    exact (ENNReal.ofReal_pos.mpr hV.1).ne' hz
  have hne1 : ¬E =ᵐ[torusVolume] (univ : Set Torus) := by
    intro h
    have ho := measure_congr h
    rw [torusVolume_univ,hmin.2.1] at ho
    have hv := congrArg ENNReal.toReal ho
    rw [ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_one] at hv
    linarith [hV.2]
  rcases hB with hB|hB <;> rcases hD with hD|hD
  · exfalso; apply hne1
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    exact iff_of_true (hxu.mpr (hx.elim (fun hb ↦ hB hb) (fun hd ↦ hD hd))) (mem_univ x)
  · left
    filter_upwards [hEU,hpart] with x hxu hx
    change (x∈E)=(x∈B)
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu ↦ hx.resolve_right (fun hd ↦ hD hd hu),fun hb ↦ hB hb⟩
  · right
    filter_upwards [hEU,hpart] with x hxu hx
    change (x∈E)=(x∈Bᶜ)
    apply propext
    exact (Iff.of_eq hxu).trans ⟨fun hu hb ↦ hB hb hu,fun hb ↦ hD (hx.resolve_left hb)⟩
  · exfalso; apply hne0
    filter_upwards [hEU,hpart] with x hxu hx
    apply propext
    exact iff_of_false (fun he ↦ hx.elim (fun hb ↦ hB hb (hxu.mp he)) (fun hd ↦ hD hd (hxu.mp he))) (fun h ↦ h)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusCoordinatePermute_measurePreserving (e : Fin 3 ≃ Fin 3) :
    MeasurePreserving (torusCoordinatePermute e) torusVolume torusVolume := by
  convert product_to_torus_measurePreserving.comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => AddCircle (1 : ℝ)) e.symm).comp
      torus_to_product_measurePreserving) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext i
  simp [Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft]

lemma quotientMap_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := rfl

lemma coverCoordinatePermute_lattice (e : Fin 3 ≃ Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinatePermute e (latticeVector m)=latticeVector (fun j => m (e j)) := rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinatePermutedField_contDiff (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinatePermutedField e F) :=
  (coverCoordinatePermute e.symm).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinatePermute e).toContinuousLinearEquiv.contDiff)

lemma coordinatePermutedField_periodic (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinatePermutedField e F (x+latticeVector n)=coordinatePermutedField e F x := by
  intro n x
  simp only [coordinatePermutedField,map_add,coverCoordinatePermute_lattice,hp]

lemma coordinatePermutedField_admissible (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinatePermutedField e F) := by
  refine ⟨coordinatePermutedField_contDiff e hF.1,coordinatePermutedField_periodic e hF.2.1,?_⟩
  intro x
  simpa only [coordinatePermutedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinatePermute e x)

lemma coordinatePermutedField_divergence (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinatePermutedField e F) x=divergence F (coverCoordinatePermute e x) := by
  have hd : HasFDerivAt (coordinatePermutedField e F)
      ((coverCoordinatePermute e.symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinatePermute e x)).comp
          (coverCoordinatePermute e).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinatePermute e.symm).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinatePermute e).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinatePermute_single,
    coverCoordinatePermute_apply]
  exact e.symm.sum_comp (fun j : Fin 3 => (fderiv ℝ F (coverCoordinatePermute e x) (EuclideanSpace.single j 1)) j)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinatePermute (e : Fin 3 ≃ Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (torusCoordinatePermute e ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinatePermutedField e.symm F) x := by
  have hm := (torusCoordinatePermute e).continuous.measurable
  have hr := coordinatePermutedField_admissible e.symm hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinatePermutedField e.symm F) (representative (torusCoordinatePermute e z))) := by
    funext z
    rw [coordinatePermutedField_divergence e.symm hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinatePermute e.symm (representative (torusCoordinatePermute e z))),
      quotientMap_coordinatePermute,quotientMap_representative]
    have hh : torusCoordinatePermute e.symm (torusCoordinatePermute e z)=z := by
      simpa only [Equiv.symm_symm] using torusCoordinatePermute_inverse e.symm z
    rw [hh]
  rw [he]
  exact (torusCoordinatePermute_measurePreserving e).setIntegral_preimage_emb
    (torusCoordinatePermute e).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinatePermutedField e.symm F) (representative z)) E

lemma perimeter_coordinatePermute_le (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinatePermute e hF hE]
  exact le_iSup_of_le (coordinatePermutedField e.symm F)
    (le_iSup_of_le (coordinatePermutedField_admissible e.symm hF) le_rfl)

lemma perimeter_coordinatePermute_measurable (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinatePermute_le e hE)
  have hh := perimeter_coordinatePermute_le e.symm ((torusCoordinatePermute e).continuous.measurable hE)
  have he : torusCoordinatePermute e.symm ⁻¹' (torusCoordinatePermute e ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

theorem perimeter_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp,← perimeter_congr_ae he]
  exact perimeter_coordinatePermute_measurable e (measurableSet_toMeasurable _ _)

lemma volume_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    torusVolume (torusCoordinatePermute e ⁻¹' E)=torusVolume E :=
  (torusCoordinatePermute_measurePreserving e).measure_preimage hE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusCoordinatePermute_norm (e : Fin 3 ≃ Fin 3) (x : Torus) :
    ‖torusCoordinatePermute e x‖=‖x‖ := by
  have h := (torusCoordinatePermute e).dist_eq x 0
  have hz : torusCoordinatePermute e 0=0 := by ext j; rfl
  simpa only [hz,dist_zero_right] using h

lemma torusAxialProjection_permute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (x : Torus) :
    torusAxialProjection (e.symm i) (torusCoordinatePermute e x)=
      torusCoordinatePermute e (torusAxialProjection i x) := by
  ext j
  simp only [torusCoordinatePermute_apply,torusAxialProjection_apply]
  have h : j=e.symm i ↔ e j=i := by
    constructor
    · intro h; rw [h,Equiv.apply_symm_apply]
    · intro h; rw [← h,Equiv.symm_apply_apply]
  simp only [h]

lemma axialTube_zero_model {r : ℝ} (hr : 0 ≤ r) : axialTube 0 0 r=UpperComparison.centeredTube r := by
  ext x
  change ‖torusAxialProjection 0 (x-0)‖ < r ↔ ‖x 1‖^2+‖x 2‖^2 < r^2
  rw [sub_zero,← sq_lt_sq₀ (norm_nonneg _) hr,PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_three]

lemma axialTube_eq_permute {r : ℝ} (hr : 0 ≤ r) (i : Fin 3) :
    axialTube i 0 r=torusCoordinatePermute (Equiv.swap (0 : Fin 3) i) ⁻¹' UpperComparison.centeredTube r := by
  rw [← axialTube_zero_model hr]
  ext x
  change ‖torusAxialProjection i (x-0)‖ < r ↔
    ‖torusAxialProjection 0 (torusCoordinatePermute (Equiv.swap (0 : Fin 3) i) x-0)‖ < r
  rw [sub_zero,sub_zero]
  have h := torusAxialProjection_permute (Equiv.swap (0 : Fin 3) i) i x
  simp only [Equiv.symm_swap,Equiv.swap_apply_right] at h
  rw [h,torusCoordinatePermute_norm]

lemma axialTube_eq_translate (i : Fin 3) (c : Torus) (r : ℝ) :
    axialTube i c r=(fun x : Torus => x+(-c)) ⁻¹' axialTube i 0 r := by
  ext x
  simp only [axialTube,mem_preimage,mem_ofPred_eq,sub_eq_add_neg,neg_zero,add_zero]

lemma axialTube_volume (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0 ≤ r) (hr : r≤1/2) :
    torusVolume (axialTube i c r)=ENNReal.ofReal (Real.pi*r^2) := by
  rw [axialTube_eq_translate,volume_translation (isOpen_axialTube i 0 r).measurableSet.nullMeasurableSet,
    axialTube_eq_permute hr0,volume_coordinatePermute _ (UpperComparison.measurableSet_centeredTube r).nullMeasurableSet,
    UpperComparison.volume_centeredTube hr0 hr]

lemma axialTube_perimeter (i : Fin 3) (c : Torus) {r : ℝ} (hr0 : 0 < r) (hr : r<1/2) :
    perimeter (axialTube i c r)=ENNReal.ofReal (2*Real.pi*r) := by
  rw [axialTube_eq_translate,perimeter_translation (isOpen_axialTube i 0 r).measurableSet.nullMeasurableSet,
    axialTube_eq_permute hr0.le,perimeter_coordinatePermute _ (UpperComparison.measurableSet_centeredTube r).nullMeasurableSet,
    UpperComparison.centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (UpperComparison.measurableSet_cubeTube r).nullMeasurableSet,
    UpperComparison.perimeter_cubeTube_eq hr0 hr]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma small_minimizer_tube_phase {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) {i : Fin 3} {c : Torus} {r : ℝ}
    (hr0 : 0 < r) (hr : r<1/2)
    (hph : E =ᵐ[torusVolume] axialTube i c r ∨ E =ᵐ[torusVolume] (axialTube i c r)ᶜ) :
    E =ᵐ[torusVolume] axialTube i c r := by
  rcases hph with h|h
  · exact h
  exfalso
  obtain ⟨F,hF,hFv,hFp⟩ := exists_bounded_competitor (V := V) ⟨hV.1.le,by linarith [hV.2]⟩
  have hP := (hmin.2.2 F hF hFv).trans hFp
  have heP : perimeter E = ENNReal.ofReal (2*Real.pi*r) :=
    (perimeter_congr_ae h).trans ((perimeter_compl (isOpen_axialTube i c r).measurableSet.nullMeasurableSet).trans
      (axialTube_perimeter i c hr0 hr))
  rw [heP] at hP
  have hP' : 2*Real.pi*r≤2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp
    simpa only [ENNReal.ofReal_ofNat] using hP
  have hv := congrArg ENNReal.toReal (measure_congr h)
  have hvb : torusVolume.real (axialTube i c r)=Real.pi*r^2 := by
    rw [Measure.real,axialTube_volume i c hr0.le hr.le,ENNReal.toReal_ofReal (by positivity)]
  change (torusVolume E).toReal=torusVolume.real (axialTube i c r)ᶜ at hv
  rw [hmin.2.1,ENNReal.toReal_ofReal hV.1.le,measureReal_compl (isOpen_axialTube i c r).measurableSet,
    hvb,Measure.real,torusVolume_univ,ENNReal.toReal_one] at hv
  have hh := mul_le_mul_of_nonneg_right hP' hr0.le
  nlinarith only [hv,hh,hV.2,hr]

lemma axialTube_isometric_model (i : Fin 3) (c : Torus) {r : ℝ} (hr : 0 ≤ r) :
    ∃ φ : Torus ≃ᵢ Torus,φ '' UpperComparison.centeredTube r=axialTube i c r := by
  let e := Equiv.swap (0 : Fin 3) i
  let p := torusCoordinatePermute e
  let φ := p.trans (IsometryEquiv.addRight c)
  have he (y : Torus) : p (φ y-c)=y := by
    change p (p y+c-c)=y
    rw [add_sub_cancel_right]
    exact (show torusCoordinatePermute e (torusCoordinatePermute e.symm y)=y from
      torusCoordinatePermute_inverse e y)
  refine ⟨φ,?_⟩
  rw [axialTube_eq_translate,axialTube_eq_permute hr]
  ext x
  change (∃ y∈UpperComparison.centeredTube r,φ y=x) ↔ p (x+(-c))∈UpperComparison.centeredTube r
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [← sub_eq_add_neg,he] using hy
  · intro hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    have hh := he (φ.symm x)
    rw [φ.apply_symm_apply] at hh
    simpa only [← sub_eq_add_neg,hh] using hx

theorem isMinimizerAt_cylindrical_standard_tube_oai {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) {c : Cover} {r : ℝ} (hr0 : 0 < r) (hr : r<1/2)
    (hbd : frontier (openRepresentative E)=quotientMap '' euclideanCylinder (EuclideanSpace.single i 1) c r) :
    4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hae := small_minimizer_tube_phase hV hmin hr0 hr
    (isMinimizerAt_cylindrical_boundary_phase hV' hE hmin i hr0 hr hbd)
  have hv := congrArg ENNReal.toReal (measure_congr hae)
  rw [hmin.2.1,axialTube_volume i (quotientMap c) hr0.le hr.le,
    ENNReal.toReal_ofReal hV.1.le,ENNReal.toReal_ofReal (by positivity)] at hv
  obtain ⟨hs0,hs,hsv⟩ := UpperComparison.canonicalBall_radius_properties hV
  let s : ℝ := (3*V/(4*Real.pi))^(1/3 : ℝ)
  change 0 < s at hs0
  change s^3*(Real.pi*4/3)=V at hsv
  have hP := isMinimizerAt_perimeter_le_candidateProfile hV' hmin
  rw [perimeter_congr_ae hae,axialTube_perimeter i (quotientMap c) hr0 hr] at hP
  have hPball : 2*Real.pi*r≤4*Real.pi*s^2 := by
    have hb : candidateProfile V≤(36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
      unfold candidateProfile
      rw [min_eq_left (by linarith [hV.2] : V≤1-V)]
      exact min_le_left _ _
    have hh := hP.trans (ENNReal.ofReal_le_ofReal hb)
    rw [← UpperComparison.ballArea_formula hV.1.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hPslab : 2*Real.pi*r≤2 := by
    have hb : candidateProfile V≤2 := (min_le_right _ _).trans (min_le_right _ _)
    have hh := hP.trans (ENNReal.ofReal_le_ofReal hb)
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ)≤2)).mp hh
  have hrs : r≤2*s^2 := by nlinarith [Real.pi_pos]
  have hrseq : r^2=(4/3)*s^3 := by
    have hz : Real.pi*(r^2-(4/3)*s^3)=0 := by nlinarith only [hv,hsv]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero)
  have hsThird : 1/3 ≤ s := by
    have hh := (sq_le_sq₀ hr0.le (by positivity : 0≤2*s^2)).mpr hrs
    have hp : 0 < s^3 := pow_pos hs0 _
    have hh' : s^3*(s-1/3)≥0 := by nlinarith only [hh,hrseq]
    have hn : 0 ≤ s-1/3 := (mul_nonneg_iff_of_pos_left hp).mp hh'
    linarith
  have hlow : 4*Real.pi/81≤V := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/3) hsThird 3
    have ht := mul_le_mul_of_nonneg_right hh (show 0≤Real.pi*4/3 by positivity)
    nlinarith only [ht,hsv]
  have hupp : V≤1/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    have hh : Real.pi*r≤1 := by linarith only [hPslab]
    have hsq := (sq_le_sq₀ (by positivity : 0≤Real.pi*r) (by norm_num : (0 : ℝ)≤1)).mpr hh
    rw [hv]
    nlinarith only [hsq]
  refine ⟨hlow,hupp,?_⟩
  have hrsqrt : r=Real.sqrt (V/Real.pi) := by
    rw [hv,mul_div_cancel_left₀ _ Real.pi_ne_zero,Real.sqrt_sq hr0.le]
  obtain ⟨φ,hφ⟩ := axialTube_isometric_model i (quotientMap c) hr0.le
  refine ⟨φ,hae.trans ?_⟩
  rw [← hφ]
  exact Filter.Eventually.of_forall (fun x => by rw [hrsqrt]; rfl)

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube_oai := @OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube_oai
