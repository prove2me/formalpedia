-- Prove2me | solution 1 for OAI.CubicTorus.actual_tangent_secondary_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:12:02.480642+00:00
-- url     : https://prove2.me/submissions/f99fa7e5-e93f-4876-b7fb-5581c6a51d43

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density

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

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

lemma characteristic_mul (E : Set Torus) (g : Cover → ℝ) (x : Cover) :
    characteristic E (quotientMap x) * g x = (quotientMap ⁻¹' E).indicator g x := by
  classical
  by_cases hx : quotientMap x ∈ E <;> simp [characteristic, hx]

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

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma smoothApprox_lipschitz {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) : LipschitzWith (smoothApproxLip n) (smoothApprox g n) := by
  have hφ := (mollifier n).contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))
  have hφc := (mollifier n).hasCompactSupport_normed (μ := volume)
  have hd (x) := hφc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))
    (locallyIntegrable_of_bounded hg hb) x
  have hdi : Integrable (fun y : Cover => ‖fderiv ℝ ((mollifier n).normed volume) y‖)
      volume :=
    (hφ.continuous_fderiv (by simp)).norm.integrable_of_hasCompactSupport (hφc.fderiv ℝ).norm
  apply lipschitzWith_of_nnnorm_fderiv_le ((smoothApprox_contDiff hg hb n).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (smoothApprox g n) x‖ ≤ _
  change ‖fderiv ℝ (((mollifier n).normed volume) ⋆ g) x‖ ≤ _
  rw [(hd x).fderiv, convolution_def]
  apply norm_integral_le_of_norm_le hdi
  exact Eventually.of_forall fun y => by
    have heq : ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Cover
        (fderiv ℝ ((mollifier n).normed volume) y)) (g (x - y)) =
        g (x - y) • fderiv ℝ ((mollifier n).normed volume) y := by
      ext v
      simp [ContinuousLinearMap.precompL_apply, mul_comm]
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb (x - y))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

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

lemma admissible_cutoff {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, f x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x ↦ f x • F x) := by
  refine ⟨hf.smul hF.1, ?_, ?_⟩
  · intro n x
    change f (x + latticeVector n) • F (x + latticeVector n) = _
    rw [hp, hF.2.1]
  · intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb x).2).trans (hF.2.2 x)

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
open scoped Topology RealInnerProductSpace

lemma cutoff_integration_by_parts {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, f x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, f x * divergence F x) =
      -(∫ x in fundamentalCube, ⟪gradient f x, F x⟫) := by
  have hi₁ : IntegrableOn (fun x ↦ f x * divergence F x) fundamentalCube :=
    integrableOn_periodic_continuous (hf.continuous.mul (continuous_divergence hF.1))
      (fun n x ↦ by rw [hp, divergence_periodic hF.2.1])
  have hi₂ : IntegrableOn (fun x ↦ ⟪gradient f x, F x⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hf).continuous.inner hF.1.continuous)
      (fun n x ↦ by rw [gradient_periodic hp, hF.2.1])
  have hz := integral_divergence_fundamentalCube (admissible_cutoff hf hp hb hF)
  simp_rw [divergence_smul_function (hf.differentiable (by simp)).differentiableAt
    (hF.1.differentiable (by simp)).differentiableAt] at hz
  rw [integral_add hi₁ hi₂] at hz
  linarith

lemma gradientCalibration_admissible {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {ε : ℝ} (hε : 0 < ε) :
    AdmissibleField (gradientCalibration f ε) := by
  have hg := gradient_contDiff hf
  have hpos (x : Cover) : 0 < ⟪gradient f x, gradient f x⟫ + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (real_inner_self_nonneg) (sq_pos_of_pos hε)
  refine ⟨?_, ?_, ?_⟩
  · exact (((ContDiff.inner ℝ hg hg).add contDiff_const).sqrt (fun x ↦ (hpos x).ne')).inv
      (fun x ↦ (Real.sqrt_pos.2 (hpos x)).ne') |>.neg |>.smul hg
  · intro n x
    dsimp only [gradientCalibration]
    rw [gradient_periodic hp]
  · intro x
    rw [gradientCalibration, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (hpos x)))]
    rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 (hpos x)), mul_one]
    apply Real.le_sqrt_of_sq_le
    rw [real_inner_self_eq_norm_sq]
    linarith [sq_nonneg ε]

lemma inner_gradientCalibration (f : Cover → ℝ) (ε : ℝ) (x : Cover) :
    ⟪gradient f x, gradientCalibration f ε x⟫ =
      -(‖gradient f x‖ ^ 2 / Real.sqrt (‖gradient f x‖ ^ 2 + ε ^ 2)) := by
  simp [gradientCalibration, inner_smul_right, div_eq_mul_inv, mul_comm]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

theorem integral_norm_gradient_le {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, f x ∈ Icc 0 1)
    {K : ℝ} (hK : ∀ F : Cover → Cover, AdmissibleField F →
      (∫ x in fundamentalCube, f x * divergence F x) ≤ K) :
    (∫ x in fundamentalCube, ‖gradient f x‖) ≤ K := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → Cover → ℝ := fun n x ↦
    ‖gradient f x‖ ^ 2 / Real.sqrt (‖gradient f x‖ ^ 2 + ε n ^ 2)
  have hgcont (n) : Continuous (g n) := by
    apply Continuous.div ((gradient_contDiff hf).continuous.norm.pow 2)
      (((gradient_contDiff hf).continuous.norm.pow 2).add continuous_const).sqrt
    intro x
    exact (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hε n)))).ne'
  have hgbd (n) (x) : ‖g n x‖ ≤ ‖gradient f x‖ := by
    have hsq : 0 < ‖gradient f x‖ ^ 2 + ε n ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hε n))
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    dsimp only [g]
    apply (div_le_iff₀ (Real.sqrt_pos.2 hsq)).2
    calc
      _ = ‖gradient f x‖ * ‖gradient f x‖ := sq _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg (ε n)])) (norm_nonneg _)
  have hglim (x) : Tendsto (fun n ↦ g n x) atTop (𝓝 ‖gradient f x‖) := by
    by_cases hz : gradient f x = 0
    · simp [g, hz]
    have hn : ‖gradient f x‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have hl := (tendsto_const_nhds (x := ‖gradient f x‖ ^ 2)).div
      (Real.continuous_sqrt.tendsto _ |>.comp ((tendsto_const_nhds (x := ‖gradient f x‖ ^ 2)).add (hεlim.pow 2)))
      (by simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq (norm_nonneg _)] using hn : Real.sqrt (‖gradient f x‖ ^ 2 + 0 ^ 2) ≠ 0)
    convert hl using 1
    · ext n
      rfl
    · simp [pow_two, hn]
  have hI : IntegrableOn (fun x ↦ ‖gradient f x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hf).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have hconv := tendsto_integral_of_dominated_convergence (fun x ↦ ‖gradient f x‖)
    (fun n ↦ (hgcont n).aestronglyMeasurable) hI
    (fun n ↦ Eventually.of_forall (hgbd n)) (Eventually.of_forall hglim)
  apply le_of_tendsto hconv
  apply Eventually.of_forall
  intro n
  have hc := gradientCalibration_admissible hf hp (hε n)
  have hi := cutoff_integration_by_parts hf hp hb hc
  simp_rw [inner_gradientCalibration, integral_neg, neg_neg] at hi
  rw [← hi]
  exact hK _ hc

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution RealInnerProductSpace

lemma characteristic_nonneg (E : Set Torus) (x : Torus) : 0 ≤ characteristic E x := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

lemma smoothApprox_characteristic_range (E : Set Torus) (n : ℕ) (x : Cover) :
    smoothApprox (characteristic E ∘ quotientMap) n x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, (le_abs_self _).trans (smoothApprox_bound
    (fun y ↦ characteristic_bound E (quotientMap y)) n x)⟩
  unfold smoothApprox
  rw [convolution_def]
  apply integral_nonneg
  intro y
  exact mul_nonneg ((mollifier n).nonneg_normed y) (characteristic_nonneg E _)

lemma characteristic_lift_periodic (E : Set Torus) (n : Fin 3 → ℤ) (x : Cover) :
    (characteristic E ∘ quotientMap) (x + latticeVector n) =
      (characteristic E ∘ quotientMap) x := by
  simp only [Function.comp_def, quotientMap_add, quotientMap_latticeVector, add_zero]

lemma torusApprox_eq_integral (E : Set Torus) (n : ℕ) (x : Torus) :
    torusApprox E n x = ∫ y : Cover, (mollifier n).normed volume y *
      characteristic E (x - quotientMap y) := by
  simp only [torusApprox, smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, Function.comp_def, quotientMap_sub, quotientMap_representative]

theorem smoothApprox_flux_le {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (n : ℕ) {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, smoothApprox (characteristic E ∘ quotientMap) n x *
      divergence F x) ≤ (perimeter E).toReal := by
  let φ : Cover → ℝ := (mollifier n).normed volume
  let D : Torus → ℝ := fun x ↦ divergence F (representative x)
  let d : Torus × Cover → ℝ := fun z ↦ characteristic E (z.1 - quotientMap z.2) * D z.1
  have hDm : Measurable D := (continuous_divergence hF.1).measurable.comp measurable_representative
  obtain ⟨M, _, hDb⟩ := periodic_bounded (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hd : Measurable d :=
    (((measurable_characteristic hE).comp
      (measurable_fst.sub (measurable_quotientMap.comp measurable_snd))).mul
        (hDm.comp measurable_fst))
  have hdm (z : Torus × Cover) : |d z| ≤ M := by
    dsimp only [d]
    rw [abs_mul]
    calc
      _ ≤ 1 * |D z.1| := mul_le_mul_of_nonneg_right (characteristic_bound E _) (abs_nonneg _)
      _ ≤ M := by simpa [D, Real.norm_eq_abs] using hDb (representative z.1)
  have hφ : Integrable φ volume := (mollifier n).integrable_normed
  have hbase : Integrable (fun z : Torus × Cover ↦ φ z.2) (torusVolume.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := torusVolume)).mul_prod hφ
  have hprod : Integrable (fun z : Torus × Cover ↦ φ z.2 * d z) (torusVolume.prod volume) :=
    hbase.mul_bdd hd.aestronglyMeasurable (Eventually.of_forall hdm)
  have hinner (y : Cover) : (∫ x, d (x, y) ∂torusVolume) ≤ (perimeter E).toReal := by
    let B : Set Torus := (fun x : Torus ↦ x + -(quotientMap y)) ⁻¹' E
    have hmB : MeasurableSet B := (measurable_id.add_const _) hE
    have hPB : perimeter B = perimeter E := perimeter_translation hE.nullMeasurableSet _
    have hEq : (fun x ↦ d (x, y)) = B.indicator D := by
      funext x
      classical
      by_cases hx : x ∈ B
      · have hx' : x - quotientMap y ∈ E := by simpa [B, sub_eq_add_neg] using hx
        simp [d, characteristic, hx, hx']
      · have hx' : x - quotientMap y ∉ E := by simpa [B, sub_eq_add_neg] using hx
        simp [d, characteristic, hx, hx']
    rw [hEq, integral_indicator hmB,
      setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hmB]
    have hh := abs_flux_le_perimeter (hPB ▸ hP) hF
    rw [hPB] at hh
    exact (le_abs_self _).trans hh
  have hSwap : (∫ x, torusApprox E n x * D x ∂torusVolume) =
      ∫ y : Cover, φ y * (∫ x, d (x, y) ∂torusVolume) := by
    simp_rw [torusApprox_eq_integral, ← integral_mul_const, mul_assoc]
    rw [integral_integral_swap hprod]
    congr 1
    funext y
    exact integral_const_mul _ _
  have hI : (∫ x, torusApprox E n x * D x ∂torusVolume) ≤ (perimeter E).toReal := by
    rw [hSwap]
    calc
      _ ≤ ∫ y : Cover, φ y * (perimeter E).toReal := by
        apply integral_mono
        · simpa only [Function.comp_def, Prod.swap_prod_mk, integral_const_mul] using hprod.swap.integral_prod_left
        · exact hφ.mul_const _
        · intro y
          exact mul_le_mul_of_nonneg_left (hinner y) ((mollifier n).nonneg_normed y)
      _ = _ := by rw [integral_mul_const, (mollifier n).integral_normed, one_mul]
  have hsc := smoothApprox_contDiff ((measurable_characteristic hE).comp measurable_quotientMap)
    (fun x ↦ characteristic_bound E (quotientMap x)) n
  have hsp := smoothApprox_periodic (characteristic_lift_periodic E) n
  have heq := setIntegral_lift (hsc.continuous.mul (continuous_divergence hF.1))
    (fun k x ↦ by simp only [Pi.mul_apply]; rw [hsp, divergence_periodic hF.2.1]) MeasurableSet.univ
  simp only [setIntegral_univ, preimage_univ, inter_univ] at heq
  exact heq ▸ hI

theorem smoothApprox_gradient_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (n : ℕ) :
    (∫ x in fundamentalCube, ‖gradient (smoothApprox (characteristic E ∘ quotientMap) n) x‖)
      ≤ (perimeter E).toReal := by
  apply integral_norm_gradient_le
    (smoothApprox_contDiff ((measurable_characteristic hE).comp measurable_quotientMap)
      (fun x ↦ characteristic_bound E (quotientMap x)) n)
    (smoothApprox_periodic (characteristic_lift_periodic E) n)
    (smoothApprox_characteristic_range E n)
  intro F hF
  exact smoothApprox_flux_le hE hP n hF

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma smoothApprox_flux_tendsto {E : Set Torus} (hE : MeasurableSet E)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    Tendsto (fun n ↦ ∫ x in fundamentalCube,
      smoothApprox (characteristic E ∘ quotientMap) n x * divergence F x) atTop
      (𝓝 (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x)) := by
  have hg := (measurable_characteristic hE).comp measurable_quotientMap
  have hb := fun x ↦ characteristic_bound E (quotientMap x)
  have hf n := smoothApprox_contDiff hg hb n
  have ht := tendsto_integral_of_dominated_convergence (fun x ↦ |divergence F x|)
    (fun n ↦ ((hf n).continuous.mul (continuous_divergence hF.1)).aestronglyMeasurable)
    (integrableOn_divergence hF.1).abs
    (fun n ↦ Eventually.of_forall (fun x ↦ by
      change ‖smoothApprox (characteristic E ∘ quotientMap) n x * divergence F x‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (smoothApprox_bound hb n x)))
    (by
      filter_upwards [ae_restrict_of_ae (smoothApprox_ae_tendsto hg hb)] with x hx
      exact hx.mul_const (divergence F x))
  simpa! only [Pi.mul_apply, Function.comp_def, characteristic_mul,
    lift_indicator_integral hE.nullMeasurableSet] using ht

lemma smooth_flux_le_gradient {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, f x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, f x * divergence F x) ≤
      ∫ x in fundamentalCube, ‖gradient f x‖ := by
  rw [cutoff_integration_by_parts hf hp hb hF, ← integral_neg]
  apply integral_mono
  · exact (integrableOn_periodic_continuous
      ((gradient_contDiff hf).continuous.inner hF.1.continuous)
      (fun n x ↦ by rw [gradient_periodic hp, hF.2.1])).neg
  · exact integrableOn_periodic_continuous (gradient_contDiff hf).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  · intro x
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 x)))

theorem smoothApprox_gradient_tendsto {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    Tendsto (fun n ↦ ∫ x in fundamentalCube,
      ‖gradient (smoothApprox (characteristic E ∘ quotientMap) n) x‖) atTop
      (𝓝 (perimeter E).toReal) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun n ↦ ha0.trans_le (integral_nonneg fun x ↦ norm_nonneg _)
    have ha0' : 0 ≤ a := le_of_not_gt ha0
    have hh : ENNReal.ofReal a < perimeter E := by
      rw [← ENNReal.ofReal_toReal hP]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0').2 ha
    obtain ⟨F, hF⟩ := lt_iSup_iff.1 hh
    obtain ⟨hF, hflux⟩ := lt_iSup_iff.1 hF
    have hflux' : a < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0').1 hflux
    filter_upwards [(smoothApprox_flux_tendsto hE hF).eventually (eventually_gt_nhds hflux')] with n hn
    exact hn.trans_le (smooth_flux_le_gradient
      (smoothApprox_contDiff ((measurable_characteristic hE).comp measurable_quotientMap)
        (fun x ↦ characteristic_bound E (quotientMap x)) n)
      (smoothApprox_periodic (characteristic_lift_periodic E) n)
      (smoothApprox_characteristic_range E n) hF)
  · intro a ha
    exact Eventually.of_forall fun n ↦ (smoothApprox_gradient_bound hE hP n).trans_lt ha

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma measurable_normalizedVector : Measurable normalizedVector := by
  exact Measurable.ite (measurableSet_singleton (0 : Cover)) measurable_const
    (measurable_id.norm.inv.smul measurable_id)

lemma measurable_unitNormal : Measurable unitNormal := measurable_normalizedVector.subtype_mk

lemma norm_smul_normalizedVector (v : Cover) : ‖v‖ • normalizedVector v = v := by
  unfold normalizedVector
  split_ifs with hv
  · simp [hv]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

lemma measurable_smoothNormalMap {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Measurable (smoothNormalMap f) :=
  (measurable_cubeRepresentative.comp measurable_quotientMap).prodMk
    (measurable_unitNormal.comp (gradient_contDiff hf).continuous.measurable.neg)

lemma integral_smoothNormalMeasure {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (g : C(NormalBundle, ℝ)) :
    (∫ z, g z ∂(smoothNormalMeasure f hf hp : Measure NormalBundle)) =
      ∫ x in fundamentalCube, ‖gradient f x‖ * g (smoothNormalMap f x) := by
  change (∫ z, g z ∂Measure.map (smoothNormalMap f) _) = _
  rw [integral_map (measurable_smoothNormalMap hf).aemeasurable g.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (gradient_contDiff hf).continuous.norm.measurable.ennreal_ofReal
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]

lemma smoothNormalMeasure_mass {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) :
    ((smoothNormalMeasure f hf hp).mass : ℝ) =
      ∫ x in fundamentalCube, ‖gradient f x‖ := by
  have hh := integral_smoothNormalMeasure hf hp (ContinuousMap.const _ (1 : ℝ))
  simpa only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one,
    FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hh

lemma smoothNormalMeasure_flux {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, f x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, normalTest F hF.1.continuous z ∂(smoothNormalMeasure f hf hp : Measure NormalBundle)) =
      ∫ x in fundamentalCube, f x * divergence F x := by
  rw [integral_smoothNormalMeasure hf hp, cutoff_integration_by_parts hf hp hb hF,
    ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change ‖gradient f x‖ * ⟪normalizedVector (-gradient f x),
      F (representative (quotientMap x))⟫ = -⟪gradient f x, F x⟫
    rw [periodic_representative hF.2.1, ← real_inner_smul_left,
      ← norm_neg (gradient f x), norm_smul_normalizedVector, inner_neg_left]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

theorem exists_normalMeasure {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    ∃ μ : FiniteMeasure NormalBundle,
      (μ.mass : ℝ) = (perimeter E).toReal ∧
      ∀ (F : Cover → Cover) (hF : AdmissibleField F),
        (∫ z, normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
          ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  let f n := smoothApprox (characteristic E ∘ quotientMap) n
  have hf n : ContDiff ℝ (⊤ : ℕ∞) (f n) := smoothApprox_contDiff
    ((measurable_characteristic hE).comp measurable_quotientMap)
    (fun x ↦ characteristic_bound E (quotientMap x)) n
  have hp n : ∀ k x, f n (x + latticeVector k) = f n x :=
    smoothApprox_periodic (characteristic_lift_periodic E) n
  let μn n := smoothNormalMeasure (f n) (hf n) (hp n)
  let P : NNReal := ⟨(perimeter E).toReal, ENNReal.toReal_nonneg⟩
  have hbound n : (μn n).mass ≤ P := by
    rw [← NNReal.coe_le_coe]
    change ((smoothNormalMeasure (f n) (hf n) (hp n)).mass : ℝ) ≤ (perimeter E).toReal
    rw [smoothNormalMeasure_mass]
    exact smoothApprox_gradient_bound hE hP n
  obtain ⟨μ, _, hμ⟩ := (isCompact_setOfPred_finiteMeasure_le_of_compactSpace NormalBundle P).exists_mapClusterPt (show Filter.map μn atTop ≤ 𝓟 {μ | μ.mass ≤ P} from
      tendsto_principal.mpr (Eventually.of_forall hbound))
  obtain ⟨U, hUa, hU⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  refine ⟨μ, ?_, ?_⟩
  · have hmass : Tendsto (fun n ↦ ((μn n).mass : ℝ)) U (𝓝 (μ.mass : ℝ)) :=
      (continuous_subtype_val.comp FiniteMeasure.continuous_mass).continuousAt.tendsto.comp hU
    have henergy : Tendsto (fun n ↦ ((μn n).mass : ℝ)) U (𝓝 (perimeter E).toReal) := by
      simpa only [μn, smoothNormalMeasure_mass, f] using
        (smoothApprox_gradient_tendsto hE hP).mono_left hUa
    exact tendsto_nhds_unique hmass henergy
  · intro F hF
    have hinter : Tendsto (fun n ↦ ∫ z, normalTest F hF.1.continuous z
        ∂(μn n : Measure NormalBundle)) U
        (𝓝 (∫ z, normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle))) :=
      (FiniteMeasure.continuous_integral_continuousMap (normalTest F hF.1.continuous)).continuousAt.tendsto.comp hU
    have hflux : Tendsto (fun n ↦ ∫ z, normalTest F hF.1.continuous z
        ∂(μn n : Measure NormalBundle)) U
        (𝓝 (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x)) := by
      have heq n := smoothNormalMeasure_flux (hf n) (hp n)
        (smoothApprox_characteristic_range E n) hF
      simp_rw [show (fun n ↦ ∫ z, normalTest F hF.1.continuous z
          ∂(μn n : Measure NormalBundle)) = (fun n ↦ ∫ x in fundamentalCube, f n x * divergence F x)
        from funext heq]
      exact (smoothApprox_flux_tendsto hE hF).mono_left hUa
    exact tendsto_nhds_unique hinter hflux

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

lemma abs_flux_local_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ x, ‖F x‖ ≤ k)
    {B : Set Torus} (hB : MeasurableSet B) (hz : ∀ x, quotientMap x ∉ B → F x = 0) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤
      k * (spatialNormalMeasure μ : Measure Torus).real B := by
  rw [← normalMeasure_flux hμ hF hp (show 0 < k + 1 by linarith)
    (fun x ↦ (hb x).trans (by linarith))]
  let g : Torus → ℝ := B.indicator (fun _ ↦ k)
  have hg : Measurable g := measurable_const.indicator hB
  have hproj := integral_spatialNormalMeasure μ hg
  have hi : Integrable (fun z : NormalBundle ↦ g (normalProjection z)) (μ : Measure NormalBundle) :=
    Integrable.of_bound (hg.comp normalProjection_continuous.measurable).aestronglyMeasurable k
      (Eventually.of_forall fun z ↦ by
        by_cases hz : normalProjection z ∈ B <;> simp [g, hz, abs_of_nonneg hk, hk])
  have hb' : ∀ z : NormalBundle, ‖normalTest F hF.continuous z‖ ≤ g (normalProjection z) := by
    intro z
    by_cases hz' : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hz']
      calc
        _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := norm_inner_le_norm _ _
        _ ≤ k := by simpa only [z.2.property, one_mul] using hb z.1
    · have hf0 := hz z.1 hz'
      simp [g, hz', normalTest, hf0]
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb')
  rw [← hproj] at h
  simpa only [g, integral_indicator hB, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ, Real.norm_eq_abs, mul_comm] using h

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

theorem smooth_test_translation_bound_local {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) (hb : ∀ x, |f x| ≤ 1)
    {c : Torus} {r : ℝ} (hz : ∀ x, quotientMap x ∉ Metric.ball c r → f x = 0)
    (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)| ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖)) := by
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
      |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a| ≤
        ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖)) := by
    let g : Cover → ℝ := fun x ↦ f (x + t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hp' : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp [g]
      rw [add_right_comm, hp]
    have hzero (x : Cover) (hx : quotientMap x ∉ Metric.ball c (r + ‖a‖)) : g x • a = 0 := by
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
    have hh := abs_flux_local_bound hμ (hg.smul_const a)
      (fun n x ↦ by rw [hp']) (norm_nonneg a)
      (fun x ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg a) (hb _))
      Metric.isOpen_ball.measurableSet hzero
    simpa only [divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g, fderiv_comp_add_right] using hh
  calc
    _ = ‖∫ t in Ioc (0 : ℝ) 1, ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        fderiv ℝ f (x + t • a) a‖ := by
      rw [← integral_integral_swap hi]
      simp_rw [hFTC, Real.norm_eq_abs]
    _ ≤ (‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + ‖a‖))) *
        (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
      exact (Real.norm_eq_abs _).trans_le (ht t ht')
    _ = _ := by simp [Measure.real]

theorem measurable_test_translation_bound_local {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, quotientMap x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
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
  filter_upwards [mollifier_rOut_tendsto.eventually (ge_mem_nhds hs)] with n hn
  exact smooth_test_translation_bound_local hμ
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n)
    (fun x hx ↦ smoothApprox_zero_outside_ball hz n hn hx) a

lemma torus_test_translation_bound_local {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {g : Torus → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    {c : Torus} {r s : ℝ} (hs : 0 < s)
    (hz : ∀ x, x ∉ Metric.ball c r → g x = 0) (a : Cover) :
    |∫ x in E, (g (x + quotientMap a) - g x) ∂torusVolume| ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
  rw [setIntegral_lift_measurable (f := fun x => g (x + quotientMap a) - g x)
    ((hg.comp (measurable_id.add_const _)).sub hg) hE]
  have hp : ∀ n x, g (quotientMap (x + latticeVector n)) = g (quotientMap x) := by
    intro n x
    rw [quotientMap_add, quotientMap_latticeVector, add_zero]
  simpa only [Function.comp_def, quotientMap_add] using
    measurable_test_translation_bound_local hμ (hg.comp measurable_quotientMap) hp
      (fun x => hb (quotientMap x)) hs (fun x hx ↦ hz _ hx) a

theorem characteristic_translation_bound_local {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Torus) {r s : ℝ} (hs : 0 < s) (a : Torus) :
    (∫ x in Metric.ball c r, |characteristic E (x - a) - characteristic E x| ∂torusVolume) ≤
      ‖a‖ * (spatialNormalMeasure μ : Measure Torus).real (Metric.ball c (r + s + ‖a‖)) := by
  let d : Torus → ℝ := fun x ↦ characteristic E (x - a) - characteristic E x
  let g : Torus → ℝ := (Metric.ball c r).indicator d
  have hd : Measurable d := ((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)
  have hg : Measurable g := hd.indicator Metric.isOpen_ball.measurableSet
  have hbd (x) : |d x| ≤ 1 := by
    rcases characteristic_dichotomy E (x - a) with h | h <;>
      rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
  have hb (x) : |g x| ≤ 1 := by
    by_cases hx : x ∈ Metric.ball c r
    · simpa only [g, indicator_of_mem hx] using hbd x
    · simp [g, hx]
  have hz (x : Torus) (hx : x ∉ Metric.ball c r) : g x = 0 := indicator_of_notMem hx _
  have hh := torus_test_translation_bound_local hE hμ hg hb hs hz (shortestLift a)
  rw [norm_shortestLift, quotientMap_shortestLift, integral_difference_test hE hg hb] at hh
  have heq (x) : d x * g x = (Metric.ball c r).indicator (fun x ↦ |d x|) x := by
    by_cases hx : x ∈ Metric.ball c r
    · simp only [g, indicator_of_mem hx]
      rcases characteristic_dichotomy E (x - a) with h | h <;>
        rcases characteristic_dichotomy E x with h' | h' <;> simp [d, h, h']
    · simp [g, hx]
  change |∫ x, d x * g x ∂torusVolume| ≤ _ at hh
  simp_rw [heq] at hh
  rw [integral_indicator Metric.isOpen_ball.measurableSet,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg (d x))] at hh
  exact hh

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma cubeCenter_closedBall_interior {r : ℝ} (hr : r < 1/2) :
    Metric.closedBall cubeCenter r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-cubeCenter) i).trans
    (show ‖x-cubeCenter‖ ≤ r by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  simp only [PiLp.sub_apply,cubeCenter,Real.norm_eq_abs] at hh
  have ha := abs_le.mp hh
  constructor <;> linarith

end CubicTorus

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

lemma smoothApprox_sub_eq_integral {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) (x : Cover) :
    smoothApprox g n x-g x =
      ∫ y : Cover, (mollifier n).normed volume y*(g (x-y)-g x) := by
  have hi : Integrable (fun y : Cover ↦ (mollifier n).normed volume y*g (x-y)) := by
    apply (mollifier n).integrable_normed.mul_bdd
      (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    exact ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.sub_apply,id_eq] using hb (x-y)
  simp_rw [mul_sub]
  rw [integral_sub hi ((mollifier n).integrable_normed.mul_const _),
    integral_mul_const,(mollifier n).integral_normed,one_mul]
  rfl

theorem smoothApprox_error_local {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (htrans : ∀ y : Cover, ‖y‖ ≤ (mollifier n).rOut →
      (∫ x, |g (x-y)-g x| ∂η) ≤ ‖y‖*A) :
    (∫ x, |smoothApprox g n x-g x| ∂η) ≤ (mollifier n).rOut*A := by
  let φ : Cover → ℝ := (mollifier n).normed volume
  let d : Cover × Cover → ℝ := fun z ↦ |g (z.1-z.2)-g z.1|
  have hφ : Integrable φ volume := (mollifier n).integrable_normed
  have hd : Measurable d := ((hg.comp (measurable_fst.sub measurable_snd)).sub
    (hg.comp measurable_fst)).abs
  have hdb (z : Cover × Cover) : |d z| ≤ 2 := by
    simpa only [d,abs_abs] using (abs_sub _ _).trans (by linarith [hb (z.1-z.2),hb z.1])
  have hbase : Integrable (fun z : Cover × Cover ↦ φ z.2) (η.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := η)).mul_prod hφ
  have hprod : Integrable (fun z : Cover × Cover ↦ φ z.2*d z) (η.prod volume) :=
    hbase.mul_bdd hd.aestronglyMeasurable (ae_of_all _ hdb)
  have hinside (x : Cover) : |smoothApprox g n x-g x| ≤ ∫ y : Cover, φ y*d (x,y) := by
    rw [smoothApprox_sub_eq_integral hg hb]
    calc
      _ ≤ ∫ y : Cover, ‖φ y*(g (x-y)-g x)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((mollifier n).nonneg_normed y),φ,d]
  have hm : Integrable (smoothApprox g n) η := Integrable.of_bound
    (smoothApprox_contDiff hg hb n).continuous.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using smoothApprox_bound hb n x)
  have hgint : Integrable g η := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hkernel (y : Cover) : φ y*(∫ x, d (x,y) ∂η) ≤ φ y*((mollifier n).rOut*A) := by
    by_cases hy : φ y = 0
    · simp [hy]
    have hyr : ‖y‖ ≤ (mollifier n).rOut := by
      have hy' : y ∈ Metric.ball (0 : Cover) (mollifier n).rOut := by
        rw [← (mollifier n).support_normed_eq (μ := (volume : Measure Cover))]
        exact hy
      exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hy')
    exact mul_le_mul_of_nonneg_left ((htrans y hyr).trans (mul_le_mul_of_nonneg_right hyr hA))
      ((mollifier n).nonneg_normed y)
  calc
    _ ≤ ∫ x, ∫ y : Cover, φ y*d (x,y) ∂volume ∂η :=
      integral_mono (hm.sub hgint).abs hprod.integral_prod_left hinside
    _ = ∫ y : Cover, ∫ x, φ y*d (x,y) ∂η := integral_integral_swap hprod
    _ = ∫ y : Cover, φ y*(∫ x, d (x,y) ∂η) := by simp_rw [integral_const_mul]
    _ ≤ ∫ y : Cover, φ y*((mollifier n).rOut*A) := by
      apply integral_mono _ (hφ.mul_const _) hkernel
      simpa only [integral_const_mul] using hprod.integral_prod_right
    _ = _ := by rw [integral_mul_const,(mollifier n).integral_normed,one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma boundedFunctionL1_dist {η : Measure Cover} [IsFiniteMeasure η]
    {f g : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) :
    dist (boundedFunctionL1 η f hf hfb) (boundedFunctionL1 η g hg hgb) =
      ∫ x, |f x-g x| ∂η := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [(integrable_bounded_one (η := η) hf hfb).coeFn_toL1,
    (integrable_bounded_one (η := η) hg hgb).coeFn_toL1] with x hx hy
  change dist ((integrable_bounded_one hf hfb).toL1 f x)
    ((integrable_bounded_one hg hgb).toL1 g x) = _
  rw [hx,hy,Real.dist_eq]

lemma totallyBounded_local_smoothApprox {ι : Type*} {η : Measure Cover}
    {K : Set Cover} (hK : IsCompact K) [IsFiniteMeasure (η.restrict K)]
    (g : ι → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hb : ∀ i x, |g i x| ≤ 1) (n : ℕ) :
    TotallyBounded (range fun i ↦ boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable (smoothApprox_bound (hb i) n)) := by
  let ν : Measure K := Measure.comap Subtype.val η
  have hv := measurePreserving_subtype_coe (μa := η) hK.measurableSet
  change MeasurePreserving ((↑) : K → Cover) ν (η.restrict K) at hv
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (Measure.map ((↑) : K → Cover) ν) := hv.map_eq.symm ▸ inferInstance
  let : IsFiniteMeasure ν := Measure.isFiniteMeasure_of_map hv.measurable.aemeasurable
  let F : ι → BoundedContinuousFunction K ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ smoothApprox (g i) n x,
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.comp continuous_subtype_val⟩
  have hLip (i) : LipschitzWith (smoothApproxLip n) (F i) := by
    change LipschitzWith (smoothApproxLip n) (smoothApprox (g i) n ∘ (Subtype.val : K → Cover))
    simpa only [mul_one] using (smoothApprox_lipschitz (hg i) (hb i) n).comp
      (LipschitzWith.subtype_val K)
  have hequi : Equicontinuous ((↑) : range F → K → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (smoothApproxLip n)
    rintro ⟨_,i,rfl⟩
    exact hLip i
  have hbounded (f : BoundedContinuousFunction K ℝ) (x : K) (hf : f ∈ range F) :
      f x ∈ Icc (-1) 1 := by
    obtain ⟨i,rfl⟩ := hf
    exact abs_le.mp (smoothApprox_bound (hb i) n x)
  have hc := BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc
    (range F) hbounded hequi
  let B : BoundedContinuousFunction K ℝ →L[ℝ] Lp ℝ 1 ν :=
    BoundedContinuousFunction.toLp 1 ν ℝ
  have htb : TotallyBounded (B '' closure (range F)) := (hc.image B.continuous).totallyBounded
  let T := Lp.compMeasurePreserving ((↑) : K → Cover) hv (E := ℝ) (p := 1)
  apply (totallyBounded_preimage (Lp.isometry_compMeasurePreserving hv).isUniformInducing htb).subset
  rintro _ ⟨i,rfl⟩
  refine ⟨F i,subset_closure (mem_range_self i),?_⟩
  apply Lp.ext
  have hi := (integrable_bounded_one (η := η.restrict K)
    (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable (smoothApprox_bound (hb i) n)).coeFn_toL1
  have hi' : ∀ᵐ x : K ∂ν,
      boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
        (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
          (smoothApprox_bound (hb i) n) (x : Cover) = smoothApprox (g i) n x := by
    have hi'' : ∀ᵐ y ∂Measure.map ((↑) : K → Cover) ν,
        boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
          (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
            (smoothApprox_bound (hb i) n) y = smoothApprox (g i) n y := by
      rw [hv.map_eq]
      exact hi
    exact ae_of_ae_map hv.measurable.aemeasurable hi''
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
        (smoothApprox_bound (hb i) n)) hv,hi',
      BoundedContinuousFunction.coeFn_toLp 1 ν ℝ (F i)] with x hx hi hxF
  exact hxF.trans (hi.symm.trans hx.symm)

theorem totallyBounded_local_translation {ι : Type*} {η : Measure Cover}
    {K : Set Cover} (hK : IsCompact K) [IsFiniteMeasure (η.restrict K)]
    (g : ι → Cover → ℝ) (hg : ∀ i, Measurable (g i)) (hb : ∀ i x, |g i x| ≤ 1)
    {A ε₀ : ℝ} (hA : 0 ≤ A) (hε₀ : 0 < ε₀)
    (htrans : ∀ i y, ‖y‖ ≤ ε₀ →
      (∫ x in K, |g i (x-y)-g i x| ∂η) ≤ ‖y‖*A) :
    TotallyBounded (range fun i ↦ boundedFunctionL1 (η.restrict K) (g i) (hg i) (hb i)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hconv : Tendsto (fun n ↦ (mollifier n).rOut*A) atTop (𝓝 0) := by
    simpa only [zero_mul] using mollifier_rOut_tendsto.mul_const A
  obtain ⟨n,hn,hns⟩ := ((hconv.eventually (gt_mem_nhds (half_pos hε))).and
    (mollifier_rOut_tendsto.eventually (gt_mem_nhds hε₀))).exists
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp
    (totallyBounded_local_smoothApprox (η := η) hK g hg hb n) (ε/2) (half_pos hε)
  refine ⟨t,ht,?_⟩
  rintro _ ⟨i,rfl⟩
  obtain ⟨y,hy,hiy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨y,hy,?_⟩
  have hdist : dist (boundedFunctionL1 (η.restrict K) (g i) (hg i) (hb i))
      (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
        (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
          (smoothApprox_bound (hb i) n)) < ε/2 := by
    rw [dist_comm,boundedFunctionL1_dist]
    exact (smoothApprox_error_local (hg i) (hb i) hA n
      (fun y hy ↦ htrans i y (hy.trans hns.le))).trans_lt hn
  have hiy' : dist (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
        (smoothApprox_bound (hb i) n)) y < ε/2 := hiy
  exact (dist_triangle _ _ _).trans_lt (by linarith)

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

lemma blowupCharacteristic_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ) {s : ℝ} (hs : 0 < s)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (y : Cover) :
    (∫ x in Metric.ball (0 : Cover) R,
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x|) ≤
      r⁻¹^3 * ‖quotientMap (r • y)‖ *
        (spatialNormalMeasure μ : Measure Torus).real
          (Metric.ball (quotientMap c) (r*R+s+‖quotientMap (r • y)‖)) := by
  let f : Torus → ℝ := fun x ↦
    |characteristic E (x-quotientMap (r • y))-characteristic E x|
  have hf : Measurable f := (((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)).abs
  have h := characteristic_translation_bound_local hE hμ (quotientMap c) hs
    (r := r*R) (quotientMap (r • y))
  rw [integral_quotient_ball f hf c (r*R) hc,
    integral_ball_affine_scaling (fun x ↦ f (quotientMap x)) c hr R] at h
  have heq (x : Cover) : f (quotientMap (c+r • x)) =
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x| := by
    simp only [f,blowupCharacteristic, ← quotientMap_sub, smul_sub]
    congr 3
    abel_nf
  simp_rw [heq] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hr.le 3))
  simpa [mul_assoc,hr.ne'] using hh

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

lemma blowupCharacteristic_translation_density {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r : ℝ} (hr : 0 < r) {R : ℝ} (hR : 0 ≤ R)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (r*(R+2))) ≤ A*(r*(R+2))^2)
    (y : Cover) (hy : ‖y‖ ≤ 1) :
    (∫ x in Metric.ball (0 : Cover) R,
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x|) ≤
      ‖y‖ * (A*(R+2)^2) := by
  have hq : ‖quotientMap (r • y)‖ ≤ r*‖y‖ := by
    simpa only [norm_smul,Real.norm_of_nonneg hr.le] using norm_quotientMap_le (r • y)
  have hqr : ‖quotientMap (r • y)‖ ≤ r :=
    hq.trans (by simpa using mul_le_mul_of_nonneg_left hy hr.le)
  have hb : r*R+r+‖quotientMap (r • y)‖ ≤ r*(R+2) := by nlinarith
  have hm := (measureReal_mono (μ := (spatialNormalMeasure μ : Measure Torus))
    (Metric.ball_subset_ball hb)).trans harea
  have h := (blowupCharacteristic_translation_bound hE hμ c hr R hr hc y).trans
    (mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) 3) (norm_nonneg _)))
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq (pow_nonneg (inv_nonneg.mpr hr.le) 3))
    (mul_nonneg hA (sq_nonneg (r*(R+2))))
  apply h.trans (h'.trans_eq _)
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma boundedFunctionL1_ae {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) :
    boundedFunctionL1 η g hg hb =ᵐ[η] g := (integrable_bounded_one hg hb).coeFn_toL1

theorem exists_cover_indicator_limit {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) (hphase : ∀ i x, g i x = 0 ∨ g i x = 1)
    (ht : TotallyBounded (range fun i ↦ boundedFunctionL1 η (g i) (hg i) (hgb i))) :
    ∃ F : Set Cover, ∃ hF : MeasurableSet F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ boundedFunctionL1 η (g (φ i)) (hg (φ i)) (hgb (φ i))) atTop
        (𝓝 (boundedFunctionL1 η (F.indicator (fun _ ↦ (1 : ℝ)))
          (measurable_const.indicator hF) (cover_indicator_bound F))) ∧
      ∀ᵐ x ∂η, Tendsto (fun i ↦ g (φ i) x) atTop
        (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  let gs (i) := boundedFunctionL1 η (g i) (hg i) (hgb i)
  obtain ⟨f,_,ns,hns,hconv⟩ := (ht.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun i ↦ subset_closure (mem_range_self i))
  obtain ⟨ms,hms,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂η, ∀ i, gs (ns (ms i)) x = g (ns (ms i)) x :=
    ae_all_iff.mpr (fun i ↦ boundedFunctionL1_ae (hg _) (hgb _))
  have hlim : ∀ᵐ x ∂η, Tendsto (fun i ↦ g (ns (ms i)) x) atTop (𝓝 (f x)) := by
    filter_upwards [hae,hcoe] with x hx hh
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    exact (hh i).symm
  let F : Set Cover := {x | f x = 1}
  have hF : MeasurableSet F := (Lp.stronglyMeasurable f).measurable (measurableSet_singleton 1)
  have hchar : f =ᵐ[η] F.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hf : f x ∈ ({0,1} : Set ℝ) := by
      apply ((finite_singleton (1 : ℝ)).insert 0).isClosed.mem_of_tendsto hx
      exact Eventually.of_forall fun i ↦ by
        rcases hphase (ns (ms i)) x with h|h <;> simp [h]
    rcases mem_insert_iff.mp hf with h0|h1
    · have hxF : x ∉ F := by simp [F,h0]
      simp [hxF,h0]
    · have hxF : x ∈ F := h1
      simp [hxF,show f x = 1 from h1]
  have heq : f = boundedFunctionL1 η (F.indicator (fun _ ↦ (1 : ℝ)))
      (measurable_const.indicator hF) (cover_indicator_bound F) :=
    Lp.ext (hchar.trans (boundedFunctionL1_ae (measurable_const.indicator hF)
      (cover_indicator_bound F)).symm)
  refine ⟨F,hF,ns ∘ ms,hns.comp hms,?_,?_⟩
  · simpa only [Function.comp_def,heq] using hconv.comp hms.tendsto_atTop
  · filter_upwards [hlim,hchar] with x hx hh
    simpa only [Function.comp_apply,← hh] using hx

lemma boundedFunctionL1_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i)) (hgb : ∀ i x, |g i x| ≤ 1)
    {f : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ boundedFunctionL1 η (g i) (hg i) (hgb i)) atTop
      (𝓝 (boundedFunctionL1 η f hf hfb))) :
    Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) atTop (𝓝 0) := by
  have h := hlim.dist (tendsto_const_nhds (x := boundedFunctionL1 η f hf hfb))
  simpa only [dist_self,boundedFunctionL1_dist] using h

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

theorem totallyBounded_moving_blowupCharacteristic {ι : Type*} {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ι → Cover) (r : ι → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 0 < R)
    (hc : ∀ i, Metric.ball (c i) (r i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : ∀ i, (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap (c i)) (r i*((R+1)+2))) ≤ A*(r i*((R+1)+2))^2) :
    TotallyBounded (range fun i ↦ boundedFunctionL1
      (volume.restrict (Metric.closedBall (0 : Cover) R)) (blowupCharacteristic E (c i) (r i))
      (measurable_blowupCharacteristic hE (c i) (r i)) (blowupCharacteristic_bound E (c i) (r i))) := by
  apply totallyBounded_local_translation (η := volume) (isCompact_closedBall _ _)
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (A := A*((R+1)+2)^2) (ε₀ := 1) (by positivity) (by norm_num)
  intro i y hy
  have htrans := blowupCharacteristic_translation_density hE hμ (c i) (hr i)
    (by linarith : 0 ≤ R+1) (hc i) hA (harea i) y hy
  apply le_trans _ htrans
  apply setIntegral_mono_set _ (ae_of_all _ fun _ ↦ abs_nonneg _)
    (ae_of_all _ fun _ hx ↦ Metric.closedBall_subset_ball (by linarith : R < R+1) hx)
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Cover) (R+1))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hf := measurable_blowupCharacteristic hE (c i) (r i)
  have hbound := blowupCharacteristic_bound E (c i) (r i)
  apply Integrable.of_bound (μ := volume.restrict (Metric.ball (0 : Cover) (R+1)))
    (((hf.comp (measurable_id.sub_const y)).sub hf).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs,abs_abs,Function.comp_apply,id_eq,Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith [hbound (x-y),hbound x])

theorem isMinimizerAt_moving_blowup_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) {d : ℝ} (hd : 0 < d)
    (hc : ∀ i, Metric.ball (c i) d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ F : Set Cover, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E (c (φ i)) (r (φ i)) x-F.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Cover) R),
        Tendsto (fun i ↦ blowupCharacteristic E (c (φ i)) (r (φ i)) x) atTop
          (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  have hsmall : 0 < min (d/(R+1)) (S/((R+1)+2)) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let cs : ℕ → Cover := fun i ↦ c (i+k)
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsb (i) : s i < min (d/(R+1)) (S/((R+1)+2)) := hk _ (by omega)
  have hchart (i) : Metric.ball (cs i) (s i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.ball_subset_ball _).trans (hc (i+k))
    exact ((lt_div_iff₀ (by linarith : 0 < R+1)).mp
      ((hsb i).trans_le (min_le_left _ _))).le
  have hb (i) : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap (cs i)) (s i*((R+1)+2))) ≤ A*(s i*((R+1)+2))^2 := by
    apply harea μ hμ _ _ (by have hh := hs i; positivity)
    exact ((lt_div_iff₀ (by linarith : 0 < (R+1)+2)).mp
      ((hsb i).trans_le (min_le_right _ _))).le
  have ht := totallyBounded_moving_blowupCharacteristic hE hμ cs s hs hR hchart hA.le hb
  obtain ⟨F,hF,φ,hφ,hconv,hae⟩ := exists_cover_indicator_limit
    (fun i ↦ blowupCharacteristic E (cs i) (s i))
    (fun i ↦ measurable_blowupCharacteristic hE (cs i) (s i))
    (fun i ↦ blowupCharacteristic_bound E (cs i) (s i))
    (fun i x ↦ characteristic_dichotomy E (quotientMap (cs i+s i • x))) ht
  refine ⟨F,hF,fun i ↦ φ i+k,fun i j hij ↦ Nat.add_lt_add_right (hφ hij) k,?_,hae⟩
  exact boundedFunctionL1_integral_tendsto
    (fun i ↦ blowupCharacteristic E (cs (φ i)) (s (φ i)))
    (fun i ↦ measurable_blowupCharacteristic hE (cs (φ i)) (s (φ i)))
    (fun i ↦ blowupCharacteristic_bound E (cs (φ i)) (s (φ i)))
    (measurable_const.indicator hF) (cover_indicator_bound F) hconv

end CubicTorus

end
end

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
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVConeSecondaryFlux
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

lemma localL1_triangle {η : Measure Cover} [IsFiniteMeasure η]
    {f g h : Cover → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) (hhb : ∀ x, |h x| ≤ 1) :
    (∫ x, |f x-h x| ∂η) ≤ (∫ x, |f x-g x| ∂η)+(∫ x, |g x-h x| ∂η) := by
  have hi := integrable_bounded_one hf hfb (η := η)
  have hj := integrable_bounded_one hg hgb (η := η)
  have hk := integrable_bounded_one hh hhb (η := η)
  rw [← integral_add (f := fun x ↦ |f x-g x|) (g := fun x ↦ |g x-h x|)
    (hi.sub hj).abs (hj.sub hk).abs]
  exact integral_mono (hi.sub hk).abs ((hi.sub hj).abs.add (hj.sub hk).abs)
    (fun x ↦ abs_sub_le (f x) (g x) (h x))

theorem actual_tangent_secondary_representation_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∃ (c : ℕ → Cover) (q : ℕ → ℝ), (∀ i, ‖c i-cubeCenter‖ ≤ 1/8) ∧
        (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun i ↦ ((i : ℝ)+1)⁻¹
  have hepos (i) : 0 < e i := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hnex (i : ℕ) : ∃ n : ℕ, i ≤ n ∧ r n < 1/(8*(‖p‖+1)) ∧
      (∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r n) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) <
          (s i)^3*e i := by
    have hp0 : 0 < (1 : ℝ)/(8*(‖p‖+1)) := by positivity
    exact ((eventually_ge_atTop i).and ((hrlim.eventually (Iio_mem_nhds hp0)).and
      (hconv.eventually (Iio_mem_nhds (mul_pos (pow_pos (hs i) 3) (hepos i)))))).exists
  choose n hn hnr hne using hnex
  have hnlim : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop b).mono (fun i hi ↦ hi.trans (hn i))
  let c : ℕ → Cover := fun i ↦ cubeCenter+r (n i) • p
  let q : ℕ → ℝ := fun i ↦ r (n i)*s i
  have hq (i) : 0 < q i := mul_pos (hr _) (hs _)
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,mul_zero,Function.comp_apply] using (hrlim.comp hnlim).mul hslim
  have hcp (i) : ‖c i-cubeCenter‖ ≤ 1/8 := by
    simp only [c,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := (lt_div_iff₀ (by positivity : 0 < 8*(‖p‖+1))).mp (hnr i)
    nlinarith [hr (n i),norm_nonneg p]
  have hc (i) : Metric.ball (c i) (1/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply Set.Subset.trans _ (cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ)<1/2))
    intro x hx
    have hxp : ‖x-c i‖ < 1/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hh := norm_add_le (x-c i) (c i-cubeCenter)
    rw [sub_add_sub_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_eq_norm] using (by linarith [hcp i] : ‖x-cubeCenter‖ ≤ 1/4)
  obtain ⟨B,hB,φ,hφ,hBconv,_⟩ := isMinimizerAt_moving_blowup_limit hV hE hmin c
    (by norm_num : (0 : ℝ)<1/8) hc q hq hqlim (by norm_num : (0 : ℝ)<1)
  have herror (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-blowupCharacteristic E (c i) (q i) x|) ≤ e i := by
    have hsub : Metric.closedBall p (s i*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
      intro x hx
      have hh : ‖x-p‖ ≤ s i := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
      have hnn := norm_add_le (x-p) p
      rw [sub_add_cancel] at hnn
      simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith [hs1 i] : ‖x‖ ≤ 2)
    have hi : IntegrableOn (fun x ↦ |blowupCharacteristic E cubeCenter (r (n i)) x-
        A.indicator (fun _ ↦ (1 : ℝ)) x|) (Metric.closedBall (0 : Cover) 2) :=
      ((integrable_bounded_one (measurable_blowupCharacteristic hE _ _) (blowupCharacteristic_bound E _ _)).sub
        (integrable_bounded_one (measurable_const.indicator hA) (cover_indicator_bound A))).abs
    have hb := (local_affine_integral_le p (hs i) hi (fun _ ↦ abs_nonneg _) hsub).trans
      (mul_le_mul_of_nonneg_left (hne i).le (pow_nonneg (inv_nonneg.mpr (hs i).le) 3))
    have heq : (s i)⁻¹^3*((s i)^3*e i)=e i := by field_simp [(hs i).ne']
    rw [heq] at hb
    simpa only [blowupCharacteristic_affine,c,q,abs_sub_comm] using hb
  refine ⟨B,hB,φ,hφ,?_, (fun i ↦ c (φ i)), (fun i ↦ q (φ i)),
    (fun i ↦ hcp (φ i)), (fun i ↦ hq (φ i)), hqlim.comp hφ.tendsto_atTop, hBconv⟩
  have hbound (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) ≤
      e (φ i)+(∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E (c (φ i)) (q (φ i)) x-B.indicator (fun _ ↦ (1 : ℝ)) x|) := by
    exact (localL1_triangle ((measurable_const.indicator hA).comp (by fun_prop))
      (measurable_blowupCharacteristic hE (c (φ i)) (q (φ i))) (measurable_const.indicator hB)
      (fun _ ↦ cover_indicator_bound A _) (blowupCharacteristic_bound E (c (φ i)) (q (φ i))) (cover_indicator_bound B)).trans
      (add_le_add (herror (φ i)) le_rfl)
  exact squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) hbound
    (by simpa using (helim.comp hφ.tendsto_atTop).add hBconv)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.actual_tangent_secondary_representation_oai := @OAI.CubicTorus.actual_tangent_secondary_representation_oai
