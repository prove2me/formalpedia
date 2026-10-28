-- Prove2me | solution 1 for OAI.CubicTorus.actual_primary_offvertex_C1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:11:28.626848+00:00
-- url     : https://prove2.me/submissions/8a3edb28-fbf5-4e71-9b5a-5b41c4888ee4

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_primary_offvertex_fixed_graphs
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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

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

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

lemma shortestLift_eq_of_lift {a : Torus} {v : Cover} (hv : quotientMap v = a)
    (hn : ‖v‖ < 1 / 2) : shortestLift a = v := by rw [← hv, shortestLift_quotientMap hn]

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

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

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

lemma normalGraph_inner {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪n, normalGraph n g y⟫ = g y := by
  simp [normalGraph, inner_add_right, normalPlaneEmbedding_inner hn,
    inner_smul_right, hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVTriangleRegion
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

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
attribute [-instance] _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma closedBall_interior {r : ℝ} (hr : r < 3/8) :
    Metric.closedBall (c : Cover) r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-(c : Cover)) i).trans
    (show ‖x-(c : Cover)‖ ≤ r from hx)
  change ‖x i-(c : Cover) i‖ ≤ r at hh
  rw [Real.norm_eq_abs,abs_le] at hh
  have hc := coords c i
  constructor <;> linarith

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVC1Patch
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

lemma normalGraph_hasFDerivWithinAt_of_flat {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : Set Torus} {S : Set Plane} {a : Torus} {x : Plane} {ν : Cover}
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) ν)
    (htrans : ⟪ν,n⟫ ≠ 0) :
    HasFDerivWithinAt g ((⟪ν,n⟫)⁻¹ •
      (-((innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap))) S x := by
  let L := (innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap
  have hz := hflat.hasFDerivWithinAt_inner_zero (normalGraph_lipschitz hn hg) hS
  have hl : HasFDerivWithinAt (fun y ↦ ⟪ν,normalPlaneEmbedding n y⟫) L S x :=
    L.hasFDerivAt.hasFDerivWithinAt
  have hh := (hz.sub hl).const_mul (⟪ν,n⟫)⁻¹
  simp only [Pi.sub_apply, normalGraph, inner_add_right, inner_smul_right,
    add_sub_cancel_left, zero_sub] at hh
  have heq : (fun y : Plane ↦ (⟪ν,n⟫)⁻¹ * (g y * ⟪ν,n⟫)) = g := by
    funext y
    field_simp
  rw [heq] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_ball_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.ball a (r*R), f x) =
      r^3 * ∫ y in Metric.ball (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.ball a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at h
  rw [h, ← integral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.ball a (r*R) ↔ x ∈ Metric.ball (0 : Cover) R := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  change (Metric.ball a (r*R)).indicator f (r • x+a) =
    (Metric.ball (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.ball (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma fundamentalCube_inter_ball_preimage (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    fundamentalCube ∩ quotientMap ⁻¹' Metric.ball (quotientMap c) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨hx,hq⟩
    rw [← quotientMap_image_ball c r] at hq
    obtain ⟨y,hy,he⟩ := hq
    have he' := quotientMap_injective_open_closed_cell
      (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩) (hc hy) he.symm
    rwa [he']
  · intro hx
    refine ⟨fun i ↦ ⟨(hc hx i).1.le,(hc hx i).2⟩,?_⟩
    rw [mem_preimage, ← quotientMap_image_ball c r]
    exact mem_image_of_mem _ hx

lemma integral_quotient_ball (f : Torus → ℝ) (hf : Measurable f)
    (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap c) r, f x ∂torusVolume) =
      ∫ x in Metric.ball c r, f (quotientMap x) := by
  rw [setIntegral_lift_measurable hf Metric.isOpen_ball.measurableSet,
    fundamentalCube_inter_ball_preimage c r hc]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_blowupCharacteristic_ball {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap c) (r*R)) =
      r^3 * ∫ x in Metric.ball (0 : Cover) R, blowupCharacteristic E c r x := by
  rw [← setIntegral_characteristic hE _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball _ (measurable_characteristic hE) c _ hc,
    integral_ball_affine_scaling _ c hr R]
  rfl

lemma localL1_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) atTop (𝓝 0))
    (s : Set Cover) :
    Tendsto (fun i ↦ ∫ x in s, g i x ∂η) atTop (𝓝 (∫ x in s, f x ∂η)) := by
  have hi (i) : Integrable (fun x ↦ |g i x-f x|) η :=
    ((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs
  have hl : Tendsto (fun i ↦ ∫ x in s, |g i x-f x| ∂η) atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ integral_nonneg (fun x ↦ abs_nonneg _)) _ hlim
    intro i
    exact setIntegral_le_integral (hi i) (ae_of_all _ (fun x ↦ abs_nonneg _))
  apply tendsto_integral_of_L1 f hf.aestronglyMeasurable
    (Eventually.of_forall (fun i ↦ integrable_bounded_one (η := η.restrict s) (hg i) (hgb i)))
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  simp only [ENNReal.ofReal_zero] at ho
  convert ho using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  symm
  simpa only [Real.norm_eq_abs,Pi.sub_apply,Function.comp_apply] using ofReal_integral_norm_eq_lintegral_enorm
    (((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).restrict (s := s))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_closedBall_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.closedBall a (r*R), f x) =
      r^3 * ∫ y in Metric.closedBall (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.closedBall a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isClosed_closedBall.measurableSet] at h
  rw [h, ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.closedBall a (r*R) ↔ x ∈ Metric.closedBall (0 : Cover) R := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_iff_right₀ hr
  change (Metric.closedBall a (r*R)).indicator f (r • x+a) =
    (Metric.closedBall (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.closedBall (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma local_affine_integral_le {f : Cover → ℝ} {S R : ℝ} (p : Cover) {r : ℝ}
    (hr : 0 < r) (hi : IntegrableOn f (Metric.closedBall (0 : Cover) S))
    (hf : ∀ x, 0 ≤ f x)
    (hsub : Metric.closedBall p (r*R) ⊆ Metric.closedBall (0 : Cover) S) :
    (∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x)) ≤
      r⁻¹^3*(∫ x in Metric.closedBall (0 : Cover) S, f x) := by
  have hs := setIntegral_mono_set hi (ae_of_all _ hf) (ae_of_all _ hsub)
  change (∫ x in Metric.closedBall p (r*R), f x) ≤
    ∫ x in Metric.closedBall (0 : Cover) S, f x at hs
  rw [integral_closedBall_affine_scaling f p hr R] at hs
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  have he : r⁻¹^3*(r^3*(∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x))) =
      ∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x) := by field_simp
  rwa [he] at hh

lemma localL1_affine_tendsto {g : ℕ → Cover → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) {S R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) S, |g i x-f x|) l (𝓝 0))
    (p : Cover) {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall p (r*R) ⊆ Metric.closedBall (0 : Cover) S) :
    Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i (p+r • x)-f (p+r • x)|) l (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
    (fun i ↦ local_affine_integral_le p hr
      (((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs)
      (fun _ ↦ abs_nonneg _) hsub)
  simpa only [mul_zero,Pi.sub_apply] using hconv.const_mul (r⁻¹^3)

lemma blowupCharacteristic_affine (E : Set Torus) (c p x : Cover) (r s : ℝ) :
    blowupCharacteristic E c r (p+s • x) =
      blowupCharacteristic E (c+r • p) (r*s) x := by
  simp [blowupCharacteristic,smul_add,mul_smul,add_assoc]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarEssentialBoundary
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_real_translate_ball {A : Set Cover} (hA : MeasurableSet A) (p : Cover) (ρ : ℝ) :
    volume.real (((fun x ↦ p+x) ⁻¹' A) ∩ Metric.ball (0 : Cover) ρ) =
      volume.real (A ∩ Metric.ball p ρ) := by
  have he (D : Set Cover) (hD : MeasurableSet D) (a : Cover) :
      (∫ x in Metric.ball a ρ, D.indicator (fun _ ↦ (1 : ℝ)) x) =
        volume.real (D ∩ Metric.ball a ρ) := by
    rw [integral_indicator hD,Measure.restrict_restrict hD,integral_const,smul_eq_mul,mul_one,
      Measure.real_def,Measure.restrict_apply_univ]
    rfl
  have hD : MeasurableSet ((fun x : Cover ↦ p+x) ⁻¹' A) :=
    hA.preimage (measurable_const.add measurable_id)
  rw [← he A hA p,← he _ hD 0]
  have hh := integral_ball_affine_scaling (A.indicator (fun _ ↦ (1 : ℝ))) p (by norm_num : (0 : ℝ)<1) ρ
  simp only [one_mul,one_pow,one_smul] at hh
  rw [hh]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  classical
  by_cases hx : p+x ∈ A <;> simp [hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_indicator_compl (A : Set Cover) (x : Cover) :
    Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x = 1-A.indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ A <;> simp [hx]

lemma blowupCharacteristic_compl (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) :
    blowupCharacteristic Eᶜ c r x = 1-blowupCharacteristic E c r x := by
  classical
  by_cases hx : quotientMap (c+r • x) ∈ E <;> simp [blowupCharacteristic,characteristic,hx]

lemma complement_blowup_error (E : Set Torus) (A : Set Cover) (c x : Cover) (r : ℝ) :
    |blowupCharacteristic Eᶜ c r x-Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x| =
      |blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x| := by
  rw [blowupCharacteristic_compl,cover_indicator_compl]
  rw [show 1-blowupCharacteristic E c r x-(1-A.indicator (fun _ ↦ (1 : ℝ)) x) =
    -(blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x) by ring,abs_neg]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma preconnected_crosses_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsPreconnected S) (hU : IsOpen U)
    (h₁ : (S ∩ U).Nonempty) (h₂ : (S ∩ Uᶜ).Nonempty) :
    (S ∩ frontier U).Nonempty := by
  classical
  by_contra h
  have hd : Disjoint (frontier U) S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    exact h ⟨x,hxs,hx⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hc := isClopen_preimage_val hU hd
  obtain ⟨x,hxS,hxU⟩ := h₁
  have he : (Subtype.val ⁻¹' U : Set S) = univ := hc.eq_univ ⟨⟨x,hxS⟩,hxU⟩
  obtain ⟨y,hyS,hyU⟩ := h₂
  have hy : (⟨y,hyS⟩ : S) ∈ Subtype.val ⁻¹' U := by rw [he]; trivial
  exact hyU hy

lemma isMinimizerAt_two_phase_frontier_in_ball {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : Cover) (r : ℝ)
    (h₁ : 0 < torusVolume.real (E ∩ Metric.ball (quotientMap c) r))
    (h₂ : 0 < torusVolume.real (Eᶜ ∩ Metric.ball (quotientMap c) r)) :
    ∃ a ∈ Metric.ball c r, quotientMap a ∈ frontier (openRepresentative E) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hp₁ : 0 < torusVolume.real (openRepresentative E ∩ Metric.ball (quotientMap c) r) := by
    convert h₁ using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg ENNReal.toReal (measure_congr (hae.inter EventuallyEq.rfl))
  have hp₂ : 0 < torusVolume.real ((openRepresentative E)ᶜ ∩ Metric.ball (quotientMap c) r) := by
    convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg ENNReal.toReal (measure_congr (hae.compl.inter EventuallyEq.rfl))
  have hcon : IsPreconnected (Metric.ball (quotientMap c) r) := by
    rw [← quotientMap_image_ball c r]
    exact (convex_ball c r).isPreconnected.image _ continuous_quotientMap.continuousOn
  obtain ⟨b,hbb,hb⟩ := preconnected_crosses_frontier hcon (isOpen_openRepresentative E)
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₁.ne')
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₂.ne')
  rw [← quotientMap_image_ball c r] at hbb
  obtain ⟨a,ha,rfl⟩ := hbb
  exact ⟨a,ha,hb⟩

end CubicTorus

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

lemma volume_real_affine_preimage_ball {A : Set Cover} (hA : MeasurableSet A)
    (p : Cover) {s : ℝ} (hs : 0 < s) (ρ : ℝ) :
    volume.real (((fun x ↦ p+s • x) ⁻¹' A) ∩ Metric.ball (0 : Cover) ρ) =
      s⁻¹^3*volume.real (A ∩ Metric.ball p (s*ρ)) := by
  have he (D : Set Cover) (hD : MeasurableSet D) (a : Cover) (r : ℝ) :
      (∫ x in Metric.ball a r, D.indicator (fun _ ↦ (1 : ℝ)) x) =
        volume.real (D ∩ Metric.ball a r) := by
    rw [integral_indicator hD,Measure.restrict_restrict hD,integral_const,smul_eq_mul,mul_one,
      Measure.real_def,Measure.restrict_apply_univ]
    rfl
  have hD : MeasurableSet ((fun x : Cover ↦ p+s • x) ⁻¹' A) :=
    hA.preimage (by fun_prop)
  rw [← he A hA p,← he _ hD 0]
  rw [integral_ball_affine_scaling _ p hs ρ]
  have hh (x : Cover) : ((fun x ↦ p+s • x) ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) x =
      A.indicator (fun _ ↦ (1 : ℝ)) (p+s • x) := rfl
  simp only [hh]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_uniform_subseq_of_bounded_modulus {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [MetricSpace Y] [ProperSpace Y]
    (f : ℕ → X → Y) (hc : ∀ i, Continuous (f i)) (y₀ : Y) (M : ℝ)
    (hb : ∀ i x, dist (f i x) y₀ ≤ M)
    (hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x y, dist x y < η → dist (f i x) (f i y) < ε) :
    ∃ (g : X → Y) (φ : ℕ → ℕ), Continuous g ∧ StrictMono φ ∧
      TendstoUniformly (fun i ↦ f (φ i)) g atTop := by
  let F : ℕ → BoundedContinuousFunction X Y := fun i ↦
    BoundedContinuousFunction.mkOfCompact ⟨f i,hc i⟩
  have heq : Equicontinuous ((↑) : range F → X → Y) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨η,hη,hηm⟩ := hm ε hε
    refine ⟨η,hη,?_⟩
    intro x y hxy
    rintro ⟨_,i,rfl⟩
    exact hηm i x y hxy
  have hcpt := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall y₀ M) (isCompact_closedBall y₀ M) (range F)
    (by rintro _ x ⟨i,rfl⟩; exact hb i x) heq
  obtain ⟨g,_,φ,hφ,hconv⟩ := hcpt.tendsto_subseq (fun i ↦ subset_closure (mem_range_self i))
  exact ⟨g,φ,g.continuous,hφ,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv⟩

lemma transverse_inner_lower {n ν : Cover} (hn : ‖n‖ = 1) (hν : ‖n-ν‖ ≤ 1/2) :
    1/2 ≤ ⟪ν,n⟫ := by
  have hh := abs_real_inner_le_norm (n-ν) n
  rw [inner_sub_left,real_inner_self_eq_norm_sq,hn,mul_one] at hh
  have hl := (abs_le.mp hh).2
  norm_num at hl
  linarith

lemma normalGraphDerivative_continuousOn {n : Cover} (hn : ‖n‖ = 1) :
    ContinuousOn (normalGraphDerivative n) (Metric.closedBall n (1/2)) := by
  have hi : ContinuousOn (fun ν : Cover ↦ (⟪ν,n⟫)⁻¹) (Metric.closedBall n (1/2)) := by
    apply (continuous_id.inner continuous_const).continuousOn.inv₀
    intro ν hν
    have hnorm : ‖n-ν‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hν
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (transverse_inner_lower hn hnorm))
  exact hi.smul ((((innerSL ℝ).continuous.continuousOn).clm_comp continuousOn_const).neg)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_CoverEssentialBoundary
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

lemma normalGraph_rescale (n : Cover) (g : Plane → ℝ) {q : ℝ} (hq : q ≠ 0) (y : Plane) :
    normalGraph n g (q • y) = q • normalGraph n (fun y ↦ q⁻¹*g (q • y)) y := by
  simp only [normalGraph,smul_add,smul_smul]
  change normalPlaneLinearIsometry n (q • y)+_ = q • normalPlaneLinearIsometry n y+_
  rw [map_smul]
  congr 1
  congr 1
  field_simp

lemma rescaled_lipschitz_graph {g : Plane → ℝ} (hg : LipschitzWith (1/4) g)
    {q : ℝ} (hq : 0 < q) : LipschitzWith (1/4) (fun y ↦ q⁻¹*g (q • y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hg.dist_le_mul (q • x) (q • y)
  rw [dist_smul₀,Real.norm_of_nonneg hq.le,Real.dist_eq] at hh
  rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hq)]
  have hi := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hq).le
  norm_num at hi ⊢
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | field_simp

theorem actual_boundary_rescaled_graph_packet {E : Set Torus} {c n : Cover}
    (hn : ‖n‖ = 1) {q e C K ρ : ℝ} (hq : 0 < q) (hCe : C*e ≤ 1/2)
    (hgraph : ActualBoundaryGraph E c n q)
    (hnormal : BoundaryNormalChart E c n (q/272) e C K ρ) :
    ∃ (b : Cover) (g : Plane → ℝ) (N : Plane → Cover),
      ‖b‖ < 1/(544*4096) ∧ LipschitzWith (1/4) g ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), |g y| ≤ 1/(544*512)) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) (1/(544*2048))) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), ‖N y‖ = 1 ∧ ‖n-N y‖ ≤ 1/2) ∧
      (∀ j : ℕ, ∀ x ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
          dist x y ≤ ρ^j/680 → dist (N x) (N y) ≤ K*e*(1/2:ℝ)^j) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (1/(544*2048)),
        HasFDerivAt g (normalGraphDerivative n (N y)) y) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        b+normalGraph n g y ∈ rescaledActualBoundary E c q) ∧
      (∀ x ∈ rescaledActualBoundary E c q ∩ Metric.ball b (1/(544*128)),
        normalGraph n g (normalPlaneCoordinates n (x-b)) = x-b) := by
  classical
  obtain ⟨a,ha,g,hg,hgc,hpoints,hcovers⟩ := hgraph
  obtain ⟨ν,hνc,hν,hνmod⟩ := hnormal
  let b := q⁻¹ • (a-c)
  let G : Plane → ℝ := fun y ↦ q⁻¹*g (q • y)
  let f : Plane → Cover := fun y ↦ a+normalGraph n g (q • y)
  let N : Plane → Cover := fun y ↦ ν (f y)
  have hb : ‖b‖ < 1/(544*4096) := by
    dsimp only [b]
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hq).le,← dist_eq_norm]
    exact (inv_mul_lt_iff₀ hq).mpr (by nlinarith)
  have hsmall (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      q • y ∈ Metric.ball (0 : Plane) ((q/544)/1024) := by
    simp only [Metric.mem_closedBall,dist_zero_right] at hy
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hq.le]
    nlinarith
  have hf : Continuous f := continuous_const.add
    ((normalGraph_lipschitz hn hg).continuous.comp (continuous_const_smul q))
  have hfpoint (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      f y ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c ((q/272)/128) := by
    have hh := hpoints (q • y) (hsmall y hy)
    refine ⟨?_,?_⟩
    · simpa only [mem_preimage,f,quotientMap_add] using hh.1
    · change dist (a+normalGraph n g (q • y)) c < (q/272)/128
      have hd := dist_triangle (a+normalGraph n g (q • y)) a c
      rw [show dist (a+normalGraph n g (q • y)) a = ‖normalGraph n g (q • y)‖ by
        rw [dist_eq_norm,add_sub_cancel_left]] at hd
      nlinarith [hh.2]
  have hNG (y : Plane) : f y = c+q • (b+normalGraph n G y) := by
    rw [show f y = a+q • normalGraph n G y from congrArg (a+·) (normalGraph_rescale n g hq.ne' y)]
    simp only [smul_add,b,smul_smul,mul_inv_cancel₀ hq.ne',one_smul]
    abel
  have hder (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) (1/(544*2048))) :
      HasFDerivAt G (normalGraphDerivative n (N y)) y := by
    have hyc := Metric.ball_subset_closedBall hy
    have hνy := hν (f y) (hfpoint y hyc)
    have ht : ⟪ν (f y),n⟫ ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (transverse_inner_lower hn (hνy.2.1.trans hCe)))
    have hflat : BoundaryFlatAt (frontier (openRepresentative E))
        (quotientMap a+quotientMap (normalGraph n g (q • y))) (ν (f y)) := by
      simpa only [f,quotientMap_add] using hνy.2.2
    have hd := (normalGraph_hasFDerivWithinAt_of_flat hn hg
      (fun x hx ↦ (hpoints x hx).1) hflat ht).hasFDerivAt (Metric.isOpen_ball.mem_nhds (hsmall y hyc))
    have hd' : HasFDerivAt G
        (q⁻¹ • (normalGraphDerivative n (N y)).comp (q • ContinuousLinearMap.id ℝ Plane)) y :=
      (hd.comp y ((hasFDerivAt_id y).const_smul q)).const_mul q⁻¹
    apply hd'.congr_fderiv
    ext v
    simp [hq.ne']
  refine ⟨b,G,N,hb,rescaled_lipschitz_graph hg hq,?_,hνc.comp hf.continuousOn hfpoint,?_,?_,hder,?_,?_⟩
  · intro y hy
    have hnorm := (abs_real_inner_le_norm n (normalGraph n g (q • y)))
    rw [hn,one_mul,normalGraph_inner hn] at hnorm
    have hh := hnorm.trans_lt (hpoints _ (hsmall y hy)).2
    dsimp only [G]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hq)]
    exact le_of_lt ((inv_mul_lt_iff₀ hq).mpr (by nlinarith))
  · intro y hy
    exact ⟨(hν _ (hfpoint y hy)).1,(hν _ (hfpoint y hy)).2.1.trans hCe⟩
  · intro j x hx y hy hxy
    apply hνmod j (f x) (hfpoint x hx) (f y) (hfpoint y hy)
    have hh := (normalGraph_lipschitz hn hg).dist_le_mul (q • x) (q • y)
    rw [dist_smul₀,Real.norm_of_nonneg hq.le] at hh
    change dist (a+normalGraph n g (q • x)) (a+normalGraph n g (q • y)) ≤ _
    rw [dist_add_left]
    norm_num at hh
    nlinarith [mul_le_mul_of_nonneg_left hxy hq.le]
  · intro y hy
    change quotientMap (c+q • (b+normalGraph n G y)) ∈ frontier (openRepresentative E)
    rw [← hNG]
    exact (hfpoint y hy).1
  · intro x hx
    have he : c+q • x-a = q • (x-b) := by
      simp only [smul_sub,b,smul_smul,mul_inv_cancel₀ hq.ne',one_smul]
      abel
    have hxa : c+q • x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩
        Metric.ball a ((q/544)/128) := by
      refine ⟨hx.1,?_⟩
      have hx' : ‖x-b‖ < 1/(544*128) := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hx.2
      simp only [Metric.mem_ball,dist_eq_norm]
      rw [he,norm_smul,Real.norm_of_nonneg hq.le]
      nlinarith
    have hh := hcovers (c+q • x) hxa
    rw [he] at hh
    have hcoord : normalPlaneCoordinates n (q • (x-b)) = q • normalPlaneCoordinates n (x-b) := by

      exact (normalPlaneCoordinates n).map_smul q (x-b)
    rw [hcoord,normalGraph_rescale n g hq.ne'] at hh
    exact (smul_right_injective Cover hq.ne') hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_integral_indicator_ball {A : Set Cover} (hA : MeasurableSet A) (x : Cover) (t : ℝ) :
    (∫ y in Metric.ball x t, A.indicator (fun _ ↦ (1:ℝ)) y) =
      volume.real (A ∩ Metric.ball x t) := by
  rw [integral_indicator hA,Measure.restrict_restrict hA,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ]
  rfl

lemma localL1_set_integral_tendsto {R : ℝ} (g : ℕ → Cover → ℝ)
    (hg : ∀ i, Measurable (g i)) (hgb : ∀ i x, |g i x| ≤ 1)
    {f : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i x-f x|) atTop (𝓝 0)) {s : Set Cover} (hs : MeasurableSet s)
    (hsub : s ⊆ Metric.closedBall (0 : Cover) R) :
    Tendsto (fun i ↦ ∫ x in s, g i x) atTop (𝓝 (∫ x in s, f x)) := by
  have h := localL1_integral_tendsto g hg hgb hf hfb hlim s
  simpa only [Measure.restrict_restrict hs,inter_eq_left.mpr hsub] using h

lemma integral_blowupCharacteristic_ball_center {E : Set Torus} (hE : MeasurableSet E)
    (c p : Cover) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hc : Metric.ball (c+r • p) (r*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap (c+r • p)) (r*t)) =
      r^3 * ∫ x in Metric.ball p t, blowupCharacteristic E c r x := by
  have hh := integral_blowupCharacteristic_ball hE (c+r • p) hr t hc
  have he := integral_ball_affine_scaling (blowupCharacteristic E c r) p (by norm_num : (0:ℝ)<1) t
  have ha (y : Cover) : blowupCharacteristic E c r (p+y) =
      blowupCharacteristic E (c+r • p) r y := by
    simpa only [one_smul,mul_one] using blowupCharacteristic_affine E c p y r 1
  simp only [one_mul,one_pow,one_smul] at he
  simp_rw [ha] at he
  rw [he]
  exact hh

theorem isMinimizerAt_rescaled_boundary_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    (x : ℕ → Cover) {p : Cover} (hp : ‖p‖ < 1/2) (hxp : Tendsto x atTop (𝓝 p))
    (hboundary : ∀ᶠ i in atTop, x i ∈ rescaledActualBoundary E (c i) (r i)) :
    p ∈ coverEssentialBoundary A := by
  obtain ⟨S,b,hS,hb,hden⟩ := isMinimizerAt_two_sided_density hV hE hmin
  have hconvC : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic Eᶜ (c i) (r i) x-Aᶜ.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0) := by
    simp_rw [complement_blowup_error]
    exact hconv
  have hdensity (t : ℝ) (ht : 0 < t) (hts : t ≤ 1/2) :
      b/8*t^3 ≤ volume.real (A ∩ Metric.ball p t) ∧
      b/8*t^3 ≤ volume.real (Aᶜ ∩ Metric.ball p t) := by
    have hsub : Metric.ball p t ⊆ Metric.closedBall (0 : Cover) 1 := by
      intro y hy
      have hy' : ‖y-p‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hh := norm_add_le (y-p) p
      rw [sub_add_cancel] at hh
      simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖y‖ ≤ 1)
    have hint := localL1_set_integral_tendsto
      (fun i ↦ blowupCharacteristic E (c i) (r i))
      (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
      (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
      (measurable_const.indicator hA) (cover_indicator_bound A) hconv Metric.isOpen_ball.measurableSet hsub
    have hintc := localL1_set_integral_tendsto
      (fun i ↦ blowupCharacteristic Eᶜ (c i) (r i))
      (fun i ↦ measurable_blowupCharacteristic hE.compl (c i) (r i))
      (fun i ↦ blowupCharacteristic_bound Eᶜ (c i) (r i))
      (measurable_const.indicator hA.compl) (cover_indicator_bound Aᶜ) hconvC Metric.isOpen_ball.measurableSet hsub
    rw [cover_integral_indicator_ball hA] at hint
    rw [cover_integral_indicator_ball hA.compl] at hintc
    have hsmall : ∀ᶠ i in atTop, r i < 1/16 ∧ r i*t/2 < S := by
      have hs : Tendsto (fun i ↦ r i*t/2) atTop (𝓝 0) := by
        simpa only [zero_mul,zero_div] using (hrlim.mul_const t).div_const 2
      exact (hrlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16))).and
        (hs.eventually (Iio_mem_nhds hS))
    have hnear := hxp.eventually (Metric.ball_mem_nhds p (half_pos ht))
    have hlower : ∀ᶠ i in atTop,
        b/8*t^3 ≤ ∫ y in Metric.ball p t, blowupCharacteristic E (c i) (r i) y ∧
        b/8*t^3 ≤ ∫ y in Metric.ball p t, blowupCharacteristic Eᶜ (c i) (r i) y := by
      filter_upwards [hc,hsmall,hnear,hboundary] with i hci hri hxi hbi
      have hz : quotientMap (c i+r i • x i) ∈ volumeSupport E ∩ volumeSupport Eᶜ := by
        rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact hbi
      have hd := hden _ hz (r i*t/2) (div_pos (mul_pos (hr i) ht) (by norm_num)) hri.2.le
      have hdist : dist (quotientMap (c i+r i • x i)) (quotientMap (c i+r i • p)) < r i*t/2 := by
        rw [dist_eq_norm,← quotientMap_sub]
        apply lt_of_le_of_lt (norm_quotientMap_le _)
        rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg (hr i).le]
        have hxi' : ‖x i-p‖ < t/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hxi
        nlinarith [hr i]
      have hball : Metric.ball (quotientMap (c i+r i • x i)) (r i*t/2) ⊆
          Metric.ball (quotientMap (c i+r i • p)) (r i*t) := by
        intro z hz'
        have hh := dist_triangle z (quotientMap (c i+r i • x i)) (quotientMap (c i+r i • p))
        have hh' : dist z (quotientMap (c i+r i • x i)) < r i*t/2 := hz'
        change dist z (quotientMap (c i+r i • p)) < r i*t
        linarith
      have hcenter : ‖c i+r i • p-cubeCenter‖ ≤ 1/8 := by
        have hh := norm_add_le (c i-cubeCenter) (r i • p)
        rw [show c i-cubeCenter+r i • p = c i+r i • p-cubeCenter by abel,
          norm_smul,Real.norm_of_nonneg (hr i).le] at hh
        nlinarith [hr i]
      let d : MovingCenter.InteriorCenter := ⟨c i+r i • p,hcenter⟩
      have hcball : Metric.ball (c i+r i • p) (r i*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
        Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d)
          (by nlinarith [hr i] : r i*t < 3/8))
      have h₁ := hd.1.trans (measureReal_mono (μ := torusVolume) (inter_subset_inter Subset.rfl hball))
      have h₂ := hd.2.trans (measureReal_mono (μ := torusVolume) (inter_subset_inter Subset.rfl hball))
      rw [integral_blowupCharacteristic_ball_center hE (c i) p (hr i) t hcball] at h₁
      rw [integral_blowupCharacteristic_ball_center hE.compl (c i) p (hr i) t hcball] at h₂
      have he : b*(r i*t/2)^3 = (r i)^3*(b/8*t^3) := by ring
      rw [he] at h₁ h₂
      exact ⟨(mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp h₁,
        (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp h₂⟩
    exact ⟨ge_of_tendsto hint (hlower.mono fun _ h ↦ h.1),
      ge_of_tendsto hintc (hlower.mono fun _ h ↦ h.2)⟩
  intro t ht
  let u := min t (1/2)
  have hu : 0 < u := lt_min ht (by norm_num)
  have hh := hdensity u hu (min_le_right _ _)
  have hpos : 0 < b/8*u^3 := by positivity
  have hmono (B : Set Cover) : volume.real (B ∩ Metric.ball p u) ≤ volume.real (B ∩ Metric.ball p t) :=
    measureReal_mono (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_left _ _)))
  exact ⟨hpos.trans_le (hh.1.trans (hmono A)),hpos.trans_le (hh.2.trans (hmono Aᶜ))⟩

theorem isMinimizerAt_rescaled_frontier_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {p : Cover} (hp : ‖p‖ < 1/2) (hboundary : p ∈ coverEssentialBoundary A)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ x ∈ Metric.ball p ε, x ∈ rescaledActualBoundary E (c i) (r i) := by
  let t := min ε (1/2)
  have ht : 0 < t := lt_min hε (by norm_num)
  have ht1 : t ≤ 1/2 := min_le_right _ _
  have hsub : Metric.ball p t ⊆ Metric.closedBall (0 : Cover) 1 := by
    intro y hy
    have hy' : ‖y-p‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖y‖ ≤ 1)
  have hint := localL1_set_integral_tendsto
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv Metric.isOpen_ball.measurableSet hsub
  have hconvc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic Eᶜ (c i) (r i) x-Aᶜ.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0) := by
    simp_rw [complement_blowup_error]
    exact hconv
  have hintc := localL1_set_integral_tendsto
    (fun i ↦ blowupCharacteristic Eᶜ (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE.compl (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound Eᶜ (c i) (r i))
    (measurable_const.indicator hA.compl) (cover_indicator_bound Aᶜ) hconvc Metric.isOpen_ball.measurableSet hsub
  rw [cover_integral_indicator_ball hA] at hint
  rw [cover_integral_indicator_ball hA.compl] at hintc
  filter_upwards [hc,hrlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16)),
    hint.eventually (lt_mem_nhds (hboundary t ht).1),
    hintc.eventually (lt_mem_nhds (hboundary t ht).2)] with i hci hri hip hic
  have hcenter : ‖c i+r i • p-cubeCenter‖ ≤ 1/8 := by
    have hh := norm_add_le (c i-cubeCenter) (r i • p)
    rw [show c i-cubeCenter+r i • p = c i+r i • p-cubeCenter by abel,
      norm_smul,Real.norm_of_nonneg (hr i).le] at hh
    nlinarith [hr i]
  let d : MovingCenter.InteriorCenter := ⟨c i+r i • p,hcenter⟩
  have hcball : Metric.ball (c i+r i • p) (r i*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d)
      (by nlinarith [hr i] : r i*t < 3/8))
  have hp₁ : 0 < torusVolume.real (E ∩ Metric.ball (quotientMap (c i+r i • p)) (r i*t)) := by
    rw [integral_blowupCharacteristic_ball_center hE (c i) p (hr i) t hcball]
    exact mul_pos (pow_pos (hr i) 3) hip
  have hp₂ : 0 < torusVolume.real (Eᶜ ∩ Metric.ball (quotientMap (c i+r i • p)) (r i*t)) := by
    rw [integral_blowupCharacteristic_ball_center hE.compl (c i) p (hr i) t hcball]
    exact mul_pos (pow_pos (hr i) 3) hic
  obtain ⟨a,ha,haf⟩ := isMinimizerAt_two_phase_frontier_in_ball hV hE hmin _ _ hp₁ hp₂
  let x := (r i)⁻¹ • (a-c i)
  have he : c i+r i • x=a := by simp [x,smul_smul,(hr i).ne']
  refine ⟨x,?_,?_⟩
  · have he' : x-p = (r i)⁻¹ • (a-(c i+r i • p)) := by
      simp only [x,smul_sub,smul_add,smul_smul,inv_mul_cancel₀ (hr i).ne',one_smul]
      abel
    rw [Metric.mem_ball,dist_eq_norm,he',norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hr i)).le]
    have ha' : ‖a-(c i+r i • p)‖ < r i*t := by simpa only [Metric.mem_ball,dist_eq_norm] using ha
    exact ((inv_mul_lt_iff₀ (hr i)).mpr ha').trans_le (min_le_left _ _)
  · change quotientMap (c i+r i • x) ∈ frontier (openRepresentative E)
    rw [he]
    exact haf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normal_graph_C1_subsequence {n : Cover} (hn : ‖n‖ = 1)
    (g : ℕ → Plane → ℝ) (ν : ℕ → Plane → Cover) {R M : ℝ}
    (hg : ∀ i, LipschitzWith (1/4) (g i))
    (hbounded : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → |g i x| ≤ M)
    (hνcont : ∀ i, ContinuousOn (ν i) (Metric.closedBall (0 : Plane) R))
    (hνunit : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → ‖ν i x‖ = 1)
    (hνclose : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → ‖n-ν i x‖ ≤ 1/2)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x, x ∈ Metric.closedBall (0 : Plane) R →
        ∀ y, y ∈ Metric.closedBall (0 : Plane) R → dist x y < η → dist (ν i x) (ν i y) < ε)
    (hder : ∀ i x, x ∈ Metric.ball (0 : Plane) R →
      HasFDerivAt (g i) (normalGraphDerivative n (ν i x)) x) :
    ∃ (G : Plane → ℝ) (N : Plane → Cover) (φ : ℕ → ℕ),
      StrictMono φ ∧ LipschitzWith (1/4) G ∧
      ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) R) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) R) ∧
      (∀ x ∈ Metric.closedBall (0 : Plane) R, ‖N x‖ = 1 ∧ ‖n-N x‖ ≤ 1/2) ∧
      TendstoUniformlyOn (fun i ↦ g (φ i)) G atTop (Metric.closedBall (0 : Plane) R) ∧
      TendstoUniformlyOn (fun i ↦ ν (φ i)) N atTop (Metric.closedBall (0 : Plane) R) ∧
      ∀ x ∈ Metric.ball (0 : Plane) R, HasFDerivAt G (normalGraphDerivative n (N x)) x := by
  classical
  let D := Metric.closedBall (0 : Plane) R
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F : ℕ → D → ℝ × Cover := fun i x ↦ (g i x,ν i x)
  have hc (i : ℕ) : Continuous (F i) :=
    ((hg i).continuous.comp continuous_subtype_val).prodMk
      (continuousOn_iff_continuous_domRestrict.mp (hνcont i))
  have hb (i : ℕ) (x : D) : dist (F i x) (0 : ℝ × Cover) ≤ max M 1 := by
    rw [Prod.dist_eq]
    apply max_le
    · exact le_trans (by simpa only [F,Prod.fst_zero,Real.dist_eq,sub_zero] using hbounded i x x.property) (le_max_left _ _)
    · exact le_trans (by simpa only [F,Prod.snd_zero,dist_zero_right,hνunit i x x.property] using (le_refl (1:ℝ))) (le_max_right _ _)
  have hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i (x y : D), dist x y < η → dist (F i x) (F i y) < ε := by
    intro ε hε
    obtain ⟨η,hη,hηm⟩ := hmod ε hε
    refine ⟨min ε η,lt_min hε hη,?_⟩
    intro i x y hxy
    rw [Prod.dist_eq]
    apply max_lt
    · have ht := (hg i).dist_le_mul x y
      have hsmall : dist (x : Plane) y < ε := hxy.trans_le (min_le_left _ _)
      change dist (g i x) (g i y) < ε
      norm_num at ht
      linarith [dist_nonneg (x := (x : Plane)) (y := (y : Plane))]
    · exact hηm i x x.property y y.property (hxy.trans_le (min_le_right _ _))
  obtain ⟨f,φ,hfc,hφ,hu⟩ := exists_uniform_subseq_of_bounded_modulus F hc 0 (max M 1) hb hm
  let G₀ : Plane → ℝ := fun x ↦ if hx : x ∈ D then (f ⟨x,hx⟩).1 else 0
  let N : Plane → Cover := fun x ↦ if hx : x ∈ D then (f ⟨x,hx⟩).2 else 0
  have hgu : TendstoUniformlyOn (fun i ↦ g (φ i)) G₀ atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with i hi
    intro x hx
    have hh := hi ⟨x,hx⟩
    rw [Prod.dist_eq] at hh
    simpa only [G₀,dite_eq_left hx,F] using (max_lt_iff.mp hh).1
  have hnu : TendstoUniformlyOn (fun i ↦ ν (φ i)) N atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with i hi
    intro x hx
    have hh := hi ⟨x,hx⟩
    rw [Prod.dist_eq] at hh
    simpa only [N,dite_eq_left hx,F] using (max_lt_iff.mp hh).2
  have hGlip : LipschitzOnWith (1/4) G₀ D := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    exact le_of_tendsto ((hgu.tendsto_at hx).dist (hgu.tendsto_at hy))
      (Eventually.of_forall fun i ↦ (hg (φ i)).dist_le_mul x y)
  obtain ⟨G,hG,hGeq⟩ := hGlip.extend_real
  have hGconv : TendstoUniformlyOn (fun i ↦ g (φ i)) G atTop D := by
    apply hgu.congr_right
    exact hGeq
  have hNc : ContinuousOn N D := hnu.continuousOn
    (Frequently.of_forall (fun i ↦ hνcont (φ i)))
  have hNunit (x : Plane) (hx : x ∈ D) : ‖N x‖ = 1 := by
    apply tendsto_nhds_unique (hnu.tendsto_at hx |>.norm)
    simpa only [hνunit _ x hx] using (tendsto_const_nhds (x := (1:ℝ)) :
      Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1))
  have hNclose (x : Plane) (hx : x ∈ D) : ‖n-N x‖ ≤ 1/2 := by
    exact le_of_tendsto ((tendsto_const_nhds.sub (hnu.tendsto_at hx)).norm)
      (Eventually.of_forall fun i ↦ hνclose (φ i) x hx)
  have hmN : MapsTo N D (Metric.closedBall n (1/2)) := by
    intro x hx
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hNclose x hx
  have hderconv : TendstoUniformlyOn (fun i x ↦ normalGraphDerivative n (ν (φ i) x))
      (fun x ↦ normalGraphDerivative n (N x)) atTop D := by
    apply UniformContinuousOn.comp_tendstoUniformlyOn_eventually _ hmN
      ((isCompact_closedBall n (1/2)).uniformContinuousOn_of_continuous
        (normalGraphDerivative_continuousOn hn)) hnu
    apply Eventually.of_forall
    intro i x hx
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hνclose (φ i) x hx
  have hderG (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) R) :
      HasFDerivAt G (normalGraphDerivative n (N x)) x :=
    hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
      (hderconv.mono Metric.ball_subset_closedBall) (fun i x hx ↦ hder (φ i) x hx)
      (fun x hx ↦ hGconv.tendsto_at (Metric.ball_subset_closedBall hx)) hx
  refine ⟨G,N,φ,hφ,hG,?_,hNc,fun x hx ↦ ⟨hNunit x hx,hNclose x hx⟩,hGconv,hnu,hderG⟩
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp,fun x ↦ normalGraphDerivative n (N x),?_,fun x hx ↦ (hderG x hx).hasFDerivWithinAt⟩
  apply contDiffOn_zero.mpr
  exact ((normalGraphDerivative_continuousOn hn).comp hNc hmN).mono Metric.ball_subset_closedBall

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_residual_lipschitz {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : LipschitzWith (1/4) g) (b : Cover) :
    LipschitzWith (9/4) (fun x ↦ normalGraph n g (normalPlaneCoordinates n (x-b))-(x-b)) := by
  have ht : LipschitzWith 1 (fun x : Cover ↦ x-b) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right,NNReal.coe_one,one_mul,le_refl]
  have hh := (((normalGraph_lipschitz hn hg).comp
    ((normalPlaneCoordinates_lipschitz n).comp ht)).sub ht)
  norm_num at hh
  simpa only [map_sub] using hh

lemma normalGraph_norm_le {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖normalGraph n g y‖ ≤ ‖y‖+|g y| := by
  have hh := norm_add_le (normalPlaneEmbedding n y) (g y • n)
  simpa only [normalGraph,normalPlaneEmbedding_norm,norm_smul,Real.norm_eq_abs,hn,mul_one] using hh

theorem rescaled_actual_graph_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {n : Cover} (hn : ‖n‖ = 1) (b : ℕ → Cover) (g : ℕ → Plane → ℝ)
    (hb : ∀ i, ‖b i‖ ≤ 1/(544*4096))
    (hg : ∀ i, LipschitzWith (1/4) (g i))
    (hgb : ∀ i y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) → |g i y| ≤ 1/(544*512))
    (hpoints : ∀ i y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
      b i+normalGraph n (g i) y ∈ rescaledActualBoundary E (c i) (r i))
    (hcovers : ∀ i x, x ∈ rescaledActualBoundary E (c i) (r i) ∩ Metric.ball (b i) (1/(544*128)) →
      normalGraph n (g i) (normalPlaneCoordinates n (x-b i))=x-b i)
    (b₀ : Cover) (G : Plane → ℝ) (hG : LipschitzWith (1/4) G)
    (hbconv : Tendsto b atTop (𝓝 b₀))
    (hgconv : TendstoUniformlyOn g G atTop (Metric.closedBall (0 : Plane) (1/(544*2048)))) :
    ‖b₀‖ ≤ 1/(544*4096) ∧
    (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
      b₀+normalGraph n G y ∈ coverEssentialBoundary A) ∧
    (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
      x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b₀))=x-b₀) := by
  have hb₀ : ‖b₀‖ ≤ 1/(544*4096) := le_of_tendsto hbconv.norm (Eventually.of_forall hb)
  have hGb (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      |G y| ≤ 1/(544*512) := le_of_tendsto (hgconv.tendsto_at hy |>.abs)
        (Eventually.of_forall fun i ↦ hgb i y hy)
  have hpt (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      b₀+normalGraph n G y ∈ coverEssentialBoundary A := by
    apply isMinimizerAt_rescaled_boundary_limit hV hE hmin c r hr hrlim hc hA hconv
      (fun i ↦ b i+normalGraph n (g i) y)
    · have hy' : ‖y‖ ≤ 1/(544*2048) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
      have hh := norm_add_le b₀ (normalGraph n G y)
      have hh' := normalGraph_norm_le hn G y
      have hgy := hGb y hy
      linarith
    · change Tendsto (fun i ↦ b i+(normalPlaneEmbedding n y+g i y • n)) atTop
        (𝓝 (b₀+(normalPlaneEmbedding n y+G y • n)))
      exact hbconv.add (tendsto_const_nhds.add ((hgconv.tendsto_at hy).smul tendsto_const_nhds))
    · exact Eventually.of_forall fun i ↦ hpoints i y hy
  refine ⟨hb₀,hpt,?_⟩
  intro x hx
  have hx' : ‖x‖ < 1/(544*8192) := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hcoords (z : Cover) (hz : ‖z‖ ≤ 1/(544*4096)) :
      normalPlaneCoordinates n (x-z) ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) := by
    have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (x-z) 0
    simp only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] at hh
    have hh' := norm_sub_le x z
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith :
      ‖normalPlaneCoordinates n (x-z)‖ ≤ 1/(544*2048))
  constructor
  · intro hxA
    let F : ℕ → Cover → Cover := fun i z ↦
      normalGraph n (g i) (normalPlaneCoordinates n (z-b i))-(z-b i)
    let F₀ : Cover := normalGraph n G (normalPlaneCoordinates n (x-b₀))-(x-b₀)
    have harg : Tendsto (fun i ↦ normalPlaneCoordinates n (x-b i)) atTop
        (𝓝 (normalPlaneCoordinates n (x-b₀))) :=
      (normalPlaneCoordinates n).continuous.tendsto _ |>.comp (tendsto_const_nhds.sub hbconv)
    have heval := hgconv.tendsto_comp hG.continuous.continuousAt.continuousWithinAt
      (tendsto_nhdsWithin_iff.mpr ⟨harg,Eventually.of_forall fun i ↦ hcoords (b i) (hb i)⟩)
    have hFlim : Tendsto (fun i ↦ F i x) atTop (𝓝 F₀) := by
      apply Filter.Tendsto.sub _ (tendsto_const_nhds.sub hbconv)
      exact ((normalPlaneLinearIsometry n).continuous.tendsto _ |>.comp harg).add
        (heval.smul tendsto_const_nhds)
    have hz : ‖F₀‖=0 := by
      apply le_antisymm _ (norm_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      let δ := min (1/(544*2048)) (ε/3)
      have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
      have hap := isMinimizerAt_rescaled_frontier_approximation hV hE hmin c r hr hrlim hc hA hconv
        (by linarith : ‖x‖<1/2) hxA δ hδ
      have hevent : ∀ᶠ i in atTop, ‖F i x‖ ≤ 0+ε := by
        filter_upwards [hap] with i hi
        obtain ⟨z,hzx,hzb⟩ := hi
        have hzx' : dist z x < δ := hzx
        have hzball : z ∈ Metric.ball (b i) (1/(544*128)) := by
          have hh := dist_triangle z x (b i)
          have hxb := norm_sub_le x (b i)
          rw [dist_eq_norm x (b i)] at hh
          have hδs : δ ≤ 1/(544*2048) := min_le_left _ _
          change dist z (b i) < 1/(544*128)
          have hbi := hb i
          linarith
        have hFz : F i z=0 := sub_eq_zero.mpr (hcovers i z ⟨hzb,hzball⟩)
        have hh := (normalGraph_residual_lipschitz hn (hg i) (b i)).dist_le_mul x z
        change dist (F i x) (F i z) ≤ _ at hh
        rw [hFz,dist_zero_right,dist_comm x z] at hh
        norm_num at hh
        have hδs : δ ≤ ε/3 := min_le_right _ _
        linarith
      exact le_of_tendsto hFlim.norm hevent
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro hxe
    have hh := hpt (normalPlaneCoordinates n (x-b₀)) (hcoords b₀ hb₀)
    rw [hxe,add_sub_cancel] at hh
    exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_strong_limit_C1_graph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {n : Cover} (hn : ‖n‖ = 1) {e C K ρ : ℝ} (hρ : 0 < ρ) (hCe : C*e ≤ 1/2)
    (hpack : ∀ i, ActualBoundaryGraph E (c i) n (r i) ∧
      BoundaryNormalChart E (c i) n (r i/272) e C K ρ) :
    ∃ (b : Cover) (G : Plane → ℝ) (N : Plane → Cover),
      ‖b‖ ≤ 1/(544*4096) ∧ LipschitzWith (1/4) G ∧
      ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) (1/(544*2048))) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) (1/(544*2048))) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), ‖N y‖ = 1 ∧ ‖n-N y‖ ≤ 1/2) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (1/(544*2048)), HasFDerivAt G (normalGraphDerivative n (N y)) y) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        b+normalGraph n G y ∈ coverEssentialBoundary A) ∧
      (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
        x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b))=x-b) := by
  classical
  choose b g ν hb hg hgb hνc hν hmod hder hpoints hcovers using
    fun i ↦ actual_boundary_rescaled_graph_packet hn (hr i) hCe (hpack i).1 (hpack i).2
  obtain ⟨b₀,hb₀,ψ,hψ,hbconv⟩ := (isCompact_closedBall (0 : Cover) (1/(544*4096))).tendsto_subseq
    (fun i ↦ by simpa only [Metric.mem_closedBall,dist_zero_right] using (hb i).le)
  have hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x, x ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
        ∀ y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
          dist x y < η → dist (ν (ψ i) x) (ν (ψ i) y) < ε := by
    intro ε hε
    have hlim : Tendsto (fun j : ℕ ↦ K*e*(1/2:ℝ)^j) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (K*e)
    obtain ⟨j,hj⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
    refine ⟨ρ^j/680,by positivity,fun i x hx y hy hxy ↦ ?_⟩
    exact (hmod (ψ i) j x hx y hy hxy.le).trans_lt hj
  obtain ⟨G,N,φ,hφ,hG,hGc,hNc,hNu,hGconv,hNconv,hGder⟩ :=
    normal_graph_C1_subsequence hn (fun i ↦ g (ψ i)) (fun i ↦ ν (ψ i))
      (fun i ↦ hg (ψ i)) (fun i ↦ hgb (ψ i)) (fun i ↦ hνc (ψ i))
      (fun i x hx ↦ (hν (ψ i) x hx).1) (fun i x hx ↦ (hν (ψ i) x hx).2) hm
      (fun i ↦ hder (ψ i))
  let χ : ℕ → ℕ := ψ ∘ φ
  have hχ : Tendsto χ atTop atTop := hψ.tendsto_atTop.comp hφ.tendsto_atTop
  have hh := rescaled_actual_graph_limit hV hE hmin
    (fun i ↦ c (χ i)) (fun i ↦ r (χ i)) (fun i ↦ hr (χ i)) (hrlim.comp hχ)
    (hχ.eventually hc) hA (hconv.comp hχ) hn
    (fun i ↦ b (χ i)) (fun i ↦ g (χ i)) (fun i ↦ (hb (χ i)).le)
    (fun i ↦ hg (χ i)) (fun i ↦ hgb (χ i)) (fun i ↦ hpoints (χ i))
    (fun i ↦ hcovers (χ i)) b₀ G hG (hbconv.comp hφ.tendsto_atTop) hGconv
  exact ⟨b₀,G,N,hh.1,hG,hGc,hNc,hNu,hGder,hh.2.1,hh.2.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_real_affine_preimage_ball_center {A : Set Cover} (hA : MeasurableSet A)
    (p x : Cover) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    volume.real (((fun y ↦ p+s • y) ⁻¹' A) ∩ Metric.ball x t) =
      s⁻¹^3*volume.real (A ∩ Metric.ball (p+s • x) (s*t)) := by
  have hB : MeasurableSet ((fun y : Cover ↦ p+s • y) ⁻¹' A) := hA.preimage (by fun_prop)
  rw [← volume_real_translate_ball hB x t]
  have he : (fun y ↦ x+y) ⁻¹' ((fun y ↦ p+s • y) ⁻¹' A) =
      (fun y ↦ (p+s • x)+s • y) ⁻¹' A := by
    ext y
    simp only [mem_preimage,smul_add,add_assoc]
  rw [he,volume_real_affine_preimage_ball hA (p+s • x) hs t]

lemma coverEssentialBoundary_affine {A : Set Cover} (hA : MeasurableSet A)
    (p x : Cover) {s : ℝ} (hs : 0 < s) :
    x ∈ coverEssentialBoundary ((fun y ↦ p+s • y) ⁻¹' A) ↔
      p+s • x ∈ coverEssentialBoundary A := by
  have he (B : Set Cover) (hB : MeasurableSet B) (t : ℝ) :
      0 < volume.real (((fun y ↦ p+s • y) ⁻¹' B) ∩ Metric.ball x t) ↔
        0 < volume.real (B ∩ Metric.ball (p+s • x) (s*t)) := by
    rw [volume_real_affine_preimage_ball_center hB p x hs t]
    exact mul_pos_iff_of_pos_left (by positivity)
  constructor
  · intro hx t ht
    have hh := hx (t/s) (div_pos ht hs)
    have h₁ := (he A hA (t/s)).mp hh.1
    have h₂ := (he Aᶜ hA.compl (t/s)).mp hh.2
    have hst : s*(t/s)=t := by field_simp
    simpa only [hst] using (And.intro h₁ h₂)
  · intro hx t ht
    have hh := hx (s*t) (mul_pos hs ht)
    exact ⟨(he A hA t).mpr hh.1,(he Aᶜ hA.compl t).mpr hh.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_primary_offvertex_C1_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {σ : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : p ∈ coverEssentialBoundary A) : CoverC1BoundaryAt A p := by
  obtain ⟨n,s,e,C,K,ρ,hn,hs,hs1,he,hC,hK,hρ,hρs,hCe,hpack⟩ :=
    actual_primary_offvertex_fixed_graphs hV hE hmin hcenter hμ hH r hr hrlim hA hconv
      hcone hstationary p hp hp0 hboundary
  let B : Set Cover := (fun x ↦ p+s • x) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hsub : Metric.closedBall p (s*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
    have hh := norm_add_le (x-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 2)
  have hconvB := localL1_affine_tendsto
    (fun i ↦ measurable_blowupCharacteristic hE cubeCenter (r i))
    (fun i ↦ blowupCharacteristic_bound E cubeCenter (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv p hs hsub
  simp only [blowupCharacteristic_affine] at hconvB
  have heq (x : Cover) : A.indicator (fun _ ↦ (1:ℝ)) (p+s • x)=B.indicator (fun _ ↦ (1:ℝ)) x := rfl
  simp only [heq] at hconvB
  obtain ⟨k,hk⟩ := eventually_atTop.mp hpack
  let c : ℕ → Cover := fun i ↦ cubeCenter+r (i+k) • p
  let q : ℕ → ℝ := fun i ↦ r (i+k)*s
  have hshift : Tendsto (fun i : ℕ ↦ i+k) atTop atTop := tendsto_add_atTop_nat k
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,Function.comp_apply,zero_mul] using (hrlim.comp hshift).mul_const s
  have hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16 := by
    filter_upwards [(hrlim.comp hshift).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16))] with i hi
    change r (i+k) < 1/16 at hi
    simp only [c,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    nlinarith [hr (i+k)]
  obtain ⟨b,G,N,hb,hG,hGc,hNc,hNu,hGder,hpoints,hcovers⟩ :=
    actual_strong_limit_C1_graph hV hE hmin c q (fun i ↦ mul_pos (hr _) hs) hqlim hc hB
      (hconvB.comp hshift) hn hρ hCe (fun i ↦ hk (i+k) (by omega))
  refine ⟨n,b,s,G,hn,hs,hb,hG,hGc,?_,?_⟩
  · intro y hy
    exact (coverEssentialBoundary_affine hA p _ hs).mp (hpoints y hy)
  · intro x hx
    rw [← coverEssentialBoundary_affine hA p x hs]
    exact hcovers x hx

end CubicTorus
end
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.actual_primary_offvertex_C1_oai := @OAI.CubicTorus.actual_primary_offvertex_C1_oai
