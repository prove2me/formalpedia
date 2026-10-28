-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_paired_blowup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:00:50.112048+00:00
-- url     : https://prove2.me/submissions/1aade5e2-2297-4037-9f8e-c7b25e968e0b

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
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

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

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma continuous_tangentialDivergence {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : NormalBundle ↦ tangentialDivergence F z.1 z.2) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_divergence hF).comp hx).sub
    (continuous_normalUnit.inner
      (((hF.continuous_fderiv (by simp)).comp hx).clm_apply continuous_normalUnit))

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x
    change (F (x + latticeVector m)) i = (F x) i
    rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_wallVariation_of_function i hc hpc (hw i)
  simpa only [normalFirstVariation, hi, hf] using hH D

theorem weakCMC_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [tangent_firstVariation_of_coordinate hH hF hp hw]
  obtain ⟨C, hC, hbound⟩ := periodic_bounded hF.continuous hp
  have h := normalMeasure_flux hμ hF hp (by linarith : 0 < C + 1)
    (fun x ↦ (hbound x).trans (by linarith : C ≤ C + 1))
  exact congrArg (fun r : ℝ ↦ H * r) h.symm

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
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

lemma latticePeriodize_wall {F : Cover → Cover}
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (i : Fin 3) (x : Cover)
    (hx : x i = 0 ∨ x i = 1) : latticePeriodize F x i = 0 := by
  have he : latticePeriodize F x = 0 := by
    unfold latticePeriodize
    suffices hz : ∀ n : Fin 3 → ℤ, F (x + latticeVector n) = 0 by
      simp only [hz, tsum_zero]
    intro n
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hi := hs h i
    simp only [PiLp.add_apply, latticeVector] at hi
    rcases hx with hx | hx
    · rw [hx, zero_add] at hi
      have hlo : (0 : ℤ) < n i := by exact_mod_cast hi.1
      have hhi : n i < (1 : ℤ) := by exact_mod_cast hi.2
      omega
    · rw [hx] at hi
      have hlo : (-1 : ℤ) < n i := by exact_mod_cast (by linarith : (-1 : ℝ) < (n i : ℝ))
      have hhi : n i < (0 : ℤ) := by exact_mod_cast (by linarith : (n i : ℝ) < 0)
      omega
  rw [he]
  rfl

theorem weakCMC_local_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  have h := weakCMC_identity hμ hH (latticePeriodize_contDiff hF hc)
    (latticePeriodize_periodic F) (latticePeriodize_wall hs)
  have he (z : NormalBundle) := latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)
  have hval (z : NormalBundle) : latticePeriodize F z.1 = F z.1 := (he z).eq_of_nhds
  have hder (z : NormalBundle) : fderiv ℝ (latticePeriodize F) z.1 = fderiv ℝ F z.1 :=
    (he z).fderiv_eq
  simpa only [tangentialDivergence, divergence, hder, hval] using h

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
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

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityField_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityField a r ε) :=
  (radialDensityWeight_contDiff a r ε).smul (contDiff_id.sub contDiff_const)

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensitySlope_nonneg (a : Cover) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Cover) :
    0 ≤ radialDensitySlope a r ε x :=
  div_nonneg Real.smoothTransition.monotone.deriv_nonneg hε.le

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

lemma radialDensitySlope_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensitySlope a r ε x = 0 := by
  unfold radialDensitySlope
  rw [smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hε.le), zero_div]

lemma radialDensityField_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityField a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have hzero := radialDensityWeight_zero hr hε (le_of_lt (by simpa only [Metric.mem_closedBall,
    dist_eq_norm, not_le] using hh))
  exact hx (by simp [radialDensityField, hzero])

lemma radialDensityField_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityField a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityField_tsupport hr hε)

lemma fderiv_norm_sq_sub (a x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ ‖y - a‖ ^ 2) x v = 2 * ⟪x - a, v⟫ := by
  have h := ((hasFDerivAt_id x).sub_const a).norm_sq
  change HasFDerivAt (fun y : Cover ↦ ‖y - a‖ ^ 2) _ x at h
  rw [h.fderiv]
  simp [inner_sub_left]

lemma fderiv_radialDensityWeight (a x v : Cover) (r ε : ℝ) :
    fderiv ℝ (radialDensityWeight a r ε) x v =
      -2 * radialDensitySlope a r ε x * ⟪x - a, v⟫ := by
  have hq : DifferentiableAt ℝ (fun y : Cover ↦ ‖y - a‖ ^ 2) x :=
    ((((contDiff_id.sub contDiff_const).norm_sq ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover ↦ ‖y - a‖ ^ 2)).differentiable (by simp)) x
  unfold radialDensityWeight
  rw [fderiv_sublevelCutoff hq]
  simp only [smul_apply, neg_apply, smul_eq_mul,
    fderiv_norm_sq_sub, radialDensitySlope]
  ring

lemma divergence_sub_const (a x : Cover) : divergence (fun y : Cover ↦ y - a) x = 3 := by
  rw [divergence, fderiv_sub_const a]
  simp [EuclideanSpace.single]

lemma tangentialDivergence_radialDensityField {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) (r ε : ℝ) :
    tangentialDivergence (radialDensityField a r ε) x n =
      2 * radialDensityWeight a r ε x -
      2 * radialDensitySlope a r ε x * (‖x - a‖ ^ 2 - ⟪n, x - a⟫ ^ 2) := by
  have hf := ((radialDensityWeight_contDiff a r ε).differentiable (by simp)) x
  have hg : DifferentiableAt ℝ (fun y : Cover ↦ y - a) x := differentiableAt_id.sub_const a
  unfold tangentialDivergence radialDensityField
  rw [divergence_smul_function hf hg, divergence_sub_const, inner_gradient_left,
    fderiv_fun_smul hf hg, fderiv_sub_const a, fderiv_fun_id]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_smul_right, fderiv_radialDensityWeight, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, real_inner_comm (x - a) n]
  ring

lemma radialDensityField_flux_bound {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    |⟪n, radialDensityField a r ε x⟫| ≤ r * radialDensityWeight a r ε x := by
  by_cases hxr : r ≤ ‖x - a‖
  · simp [radialDensityField, radialDensityWeight_zero hr hε hxr]
  · rw [radialDensityField, inner_smul_right, abs_mul,
      abs_of_nonneg (radialDensityWeight_nonneg a r ε x), mul_comm r]
    apply mul_le_mul_of_nonneg_left _ (radialDensityWeight_nonneg a r ε x)
    exact (abs_real_inner_le_norm n (x - a)).trans (by simpa only [hn, one_mul] using (le_of_not_ge hxr))

lemma radialDensityField_dilation_bound {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    2 * radialDensityWeight a r ε x ≤
      tangentialDivergence (radialDensityField a r ε) x n +
        2 * r ^ 2 * radialDensitySlope a r ε x := by
  rw [tangentialDivergence_radialDensityField hn]
  have hb := radialDensitySlope_nonneg a r hε x
  by_cases hxr : r ≤ ‖x - a‖
  · rw [radialDensitySlope_zero hr hε hxr]
    ring_nf
    rfl
  · have hnorm : ‖x - a‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - a)]
    have hh := mul_le_mul_of_nonneg_left hnorm hb
    nlinarith [mul_nonneg hb (sq_nonneg ⟪n, x - a⟫)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_radialDensitySlope (a : Cover) (r ε : ℝ) :
    Continuous (radialDensitySlope a r ε) := by
  apply Continuous.div_const
  exact (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num) |>.comp
    ((continuous_const.sub ((continuous_id.sub continuous_const).norm.pow 2)).div_const ε)

lemma integrable_radialDensityWeight (μ : FiniteMeasure NormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : NormalBundle ↦ radialDensityWeight a r ε z.1) (μ : Measure NormalBundle) :=
  ((radialDensityWeight_contDiff a r ε).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integrable_radialDensitySlope (μ : FiniteMeasure NormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : NormalBundle ↦ radialDensitySlope a r ε z.1) (μ : Measure NormalBundle) :=
  ((continuous_radialDensitySlope a r ε).comp
    (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma hasDerivAt_radialDensityWeight (a x : Cover) (r ε : ℝ) :
    HasDerivAt (fun s : ℝ ↦ radialDensityWeight a s ε x)
      (2 * r * radialDensitySlope a r ε x) r := by
  have ht := ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num)
    ((r ^ 2 - ‖x - a‖ ^ 2) / ε)).hasDerivAt
  have hq := (((hasDerivAt_id r).pow 2).sub_const (‖x - a‖ ^ 2)).div_const ε
  convert! ht.comp r hq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [radialDensitySlope, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

lemma hasDerivAt_radialDensityMass (μ : FiniteMeasure NormalBundle) (a : Cover)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (radialDensityMass μ a ε)
      (∫ z, 2 * r * radialDensitySlope a r ε z.1 ∂(μ : Measure NormalBundle)) r := by
  obtain ⟨K, hK, hb⟩ := smoothTransition_exists_deriv_bound
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun z : NormalBundle ↦ radialDensityWeight a s ε z.1) (μ : Measure NormalBundle) :=
    (integrable_radialDensityWeight μ a s ε).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z : NormalBundle ↦ 2 * r * radialDensitySlope a r ε z.1) (μ : Measure NormalBundle) :=
    ((integrable_radialDensitySlope μ a r ε).const_mul _).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂(μ : Measure NormalBundle), ∀ s ∈ Ioo (r - 1) (r + 1),
      ‖2 * s * radialDensitySlope a s ε z.1‖ ≤ 2 * (|r| + 1) * K / ε := by
    filter_upwards [] with z s hs
    have hsr : |s| ≤ |r| + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self r, neg_abs_le r, hs.1, hs.2]
    have hsl : |radialDensitySlope a s ε z.1| ≤ K / ε := by
      simp only [radialDensitySlope, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb ((s ^ 2 - ‖(z.1 : Cover) - a‖ ^ 2) / ε)) hε.le
    simp only [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc
      2 * |s| * |radialDensitySlope a s ε z.1| ≤ 2 * (|r| + 1) * (K / ε) :=
        mul_le_mul (by nlinarith) hsl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall hm)
    (integrable_radialDensityWeight μ a r ε) hm' hb' (integrable_const _)
    (Eventually.of_forall fun z s _ ↦ hasDerivAt_radialDensityWeight a z.1 s ε)).2

theorem weakCMC_radialDensityMass_ode {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (2 - |H| * r) * radialDensityMass μ a ε r ≤
      r * deriv (radialDensityMass μ a ε) r := by
  let F := radialDensityField a r ε
  have hf := radialDensityField_contDiff a r ε
  have hid := weakCMC_local_identity hμ hH hf (radialDensityField_hasCompactSupport hr.le hε)
    ((radialDensityField_tsupport hr.le hε).trans hc)
  have ht : Integrable (fun z : NormalBundle ↦ tangentialDivergence F z.1 z.2)
      (μ : Measure NormalBundle) :=
    (continuous_tangentialDivergence hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfl : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover), F z.1⟫)
      (μ : Measure NormalBundle) :=
    (continuous_normalUnit.inner (hf.continuous.comp
      (continuous_subtype_val.comp continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw := integrable_radialDensityWeight μ a r ε
  have hs := integrable_radialDensitySlope μ a r ε
  have hbound := integral_mono (hw.const_mul 2) (ht.add (hs.const_mul (2 * r ^ 2)))
    (fun z : NormalBundle ↦ radialDensityField_dilation_bound z.2.property a z.1 hr.le hε)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add ht (hs.const_mul _), integral_const_mul] at hbound
  change 2 * radialDensityMass μ a ε r ≤
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) +
      2 * r ^ 2 * ∫ z, radialDensitySlope a r ε z.1 ∂(μ : Measure NormalBundle) at hbound
  rw [hid] at hbound
  have hfb : |∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)| ≤
      r * radialDensityMass μ a ε r := by
    calc
      _ ≤ ∫ z, |⟪(z.2 : Cover), F z.1⟫| ∂(μ : Measure NormalBundle) := abs_integral_le_integral_abs
      _ ≤ ∫ z, r * radialDensityWeight a r ε z.1 ∂(μ : Measure NormalBundle) :=
        integral_mono hfl.abs (hw.const_mul _)
          (fun z : NormalBundle ↦ radialDensityField_flux_bound z.2.property a z.1 hr.le hε)
      _ = _ := integral_const_mul _ _
  have hflux : H * (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) ≤
      |H| * r * radialDensityMass μ a ε r := by
    calc
      _ ≤ |H * (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle))| := le_abs_self _
      _ = |H| * |∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)| := abs_mul _ _
      _ ≤ |H| * (r * radialDensityMass μ a ε r) := mul_le_mul_of_nonneg_left hfb (abs_nonneg _)
      _ = _ := by ring
  rw [(hasDerivAt_radialDensityMass μ a hε r).deriv, integral_const_mul]
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open Set
open scoped Topology
namespace CubicTorus

lemma hasDerivAt_cmcDensityRatio {m : ℝ → ℝ} {d r k : ℝ} (hr : 0 < r)
    (hm : HasDerivAt m d r) :
    HasDerivAt (fun t : ℝ ↦ Real.exp (k * t) * m t / t ^ 2)
      (Real.exp (k * r) / r ^ 3 * (r * d + (k * r - 2) * m r)) r := by
  have he := ((hasDerivAt_id r).const_mul k).exp
  have hd := (hasDerivAt_id r).pow 2
  convert! (he.mul hm).div hd (by exact pow_ne_zero 2 hr.ne') using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply, Pi.mul_apply]
  field_simp [hr.ne']
  ring

theorem cmcDensityRatio_monotoneOn {m d : ℝ → ℝ} {k R : ℝ}
    (hd : ∀ r ∈ Ioc 0 R, HasDerivAt m (d r) r)
    (hode : ∀ r ∈ Ioc 0 R, (2 - k * r) * m r ≤ r * d r) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (k * r) * m r / r ^ 2) (Ioc 0 R) := by
  have hh (r : ℝ) (hr : r ∈ Ioc 0 R) := hasDerivAt_cmcDensityRatio hr.1 (hd r hr)
    (k := k)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 R)
    (fun r hr ↦ (hh r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hh r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  have hr' : r ∈ Ioc 0 R := interior_subset hr
  apply mul_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hr'.1.le _))
  have h := hode r hr'
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurableSet_cellBall (a : Cover) (r : ℝ) :
    MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
  Metric.isOpen_ball.measurableSet.preimage (measurable_subtype_coe.comp measurable_fst)

lemma radialDensityWeight_tendsto (a x : Cover) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ radialDensityWeight a r ε x) (𝓝[>] 0)
      (𝓝 ((Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Metric.ball a r
  · have hxr : ‖x - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hp : 0 < r ^ 2 - ‖x - a‖ ^ 2 := by nlinarith [norm_nonneg (x - a)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp)] with ε hε hεδ
    rw [indicator_of_mem hx]
    exact (Real.smoothTransition.one_of_one_le ((one_le_div hε).2 (by simpa using hεδ.le))).symm
  · have hxr : r ≤ ‖x - a‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [indicator_of_notMem hx]
    exact (radialDensityWeight_zero hr.le hε hxr).symm

lemma radialDensityMass_tendsto (μ : FiniteMeasure NormalBundle) (a : Cover)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ radialDensityMass μ a ε r) (𝓝[>] 0) (𝓝 (cellBallMass μ a r)) := by
  have hm (ε : ℝ) := (integrable_radialDensityWeight μ a r ε).aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ z ∂(μ : Measure NormalBundle), ‖radialDensityWeight a r ε z.1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : NormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const _)
    (Eventually.of_forall fun z : NormalBundle ↦ radialDensityWeight_tendsto a z.1 hr)
  have he : (fun z : NormalBundle ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) z.1) =
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r}.indicator 1 := by
    ext z
    by_cases hz : (z.1 : Cover) ∈ Metric.ball a r
    · rw [indicator_of_mem hz, indicator_of_mem
        (show z ∈ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hz)]
      rfl
    · rw [indicator_of_notMem hz, indicator_of_notMem
        (show z ∉ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hz)]
  rwa [he, integral_indicator_one (measurableSet_cellBall a r)] at ht

lemma weakCMC_radialDensityMass_monotone {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {ε R : ℝ} (hε : 0 < ε)
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (|H| * r) * radialDensityMass μ a ε r / r ^ 2) (Ioc 0 R) := by
  apply cmcDensityRatio_monotoneOn
    (d := fun r ↦ deriv (radialDensityMass μ a ε) r)
  · intro r _
    exact (hasDerivAt_radialDensityMass μ a hε r).differentiableAt.hasDerivAt
  · intro r hr
    exact weakCMC_radialDensityMass_ode hμ hH a hr.1 hε
      ((Metric.closedBall_subset_closedBall hr.2).trans hc)

theorem weakCMC_cellBallMass_monotone {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {R : ℝ}
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (|H| * r) * cellBallMass μ a r / r ^ 2) (Ioc 0 R) := by
  intro r hr s hs hrs
  have hlr := ((radialDensityMass_tendsto μ a hr.1).const_mul (Real.exp (|H| * r))).div_const (r ^ 2)
  have hls := ((radialDensityMass_tendsto μ a hs.1).const_mul (Real.exp (|H| * s))).div_const (s ^ 2)
  apply le_of_tendsto_of_tendsto hlr hls
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact weakCMC_radialDensityMass_monotone hμ hH a hε hc hr hs hrs

end CubicTorus

end
end

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

lemma compactCell_mem_quotient_ball_iff (z : CompactCell) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    quotientMap z ∈ Metric.ball (quotientMap a) r ↔ (z : Cover) ∈ Metric.ball a r := by
  constructor
  · intro hz
    rw [← quotientMap_image_ball a r] at hz
    obtain ⟨y, hy, he⟩ := hz
    have he' := quotientMap_injective_open_closed_cell (compactCell_coordinates z) (hc hy) he.symm
    rwa [he']
  · intro hz
    rw [← quotientMap_image_ball a r]
    exact ⟨z, hz, rfl⟩

lemma cellBallMass_eq_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    cellBallMass μ a r = (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) := by
  unfold cellBallMass
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle) (Metric.ball (quotientMap a) r)).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext z
  exact (compactCell_mem_quotient_ball_iff z.1 a r hc).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_density_of_cmc_monotone {m : ℝ → ℝ} {k R : ℝ} (hR : 0 < R)
    (hm : ∀ r ∈ Ioc 0 R, 0 ≤ m r)
    (hmono : MonotoneOn (fun r : ℝ ↦ Real.exp (k * r) * m r / r ^ 2) (Ioc 0 R)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto (fun r : ℝ ↦ m r / r ^ 2) (𝓝[>] 0) (𝓝 θ) := by
  let f : ℝ → ℝ := fun r ↦ Real.exp (k * r) * m r / r ^ 2
  have hne : (Ioo (0 : ℝ) R).Nonempty := nonempty_Ioo.mpr hR
  have hb : BddBelow (f '' Ioo 0 R) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hm r ⟨hr.1, hr.2.le⟩)) (sq_nonneg _)
  have hf := (hmono.mono Ioo_subset_Ioc_self).tendsto_nhdsWithin_Ioo_right hne hb
  have he : Tendsto (fun r : ℝ ↦ Real.exp (k * r)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hc : Continuous (fun r : ℝ ↦ Real.exp (k * r)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine ⟨sInf (f '' Ioo 0 R), ?_, ?_⟩
  · exact le_csInf (hne.image _) (by
      rintro _ ⟨r, hr, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hm r ⟨hr.1, hr.2.le⟩)) (sq_nonneg _))
  · have hh := hf.div he (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun r : ℝ ↦ f r / Real.exp (k * r)) = (fun r : ℝ ↦ m r / r ^ 2) := by
      ext r
      dsimp only [f]
      rw [mul_div_assoc, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]
    change Tendsto (fun r : ℝ ↦ f r / Real.exp (k * r)) (𝓝[>] 0)
      (𝓝 (sInf (f '' Ioo 0 R) / 1)) at hh
    rwa [heq, div_one] at hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
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

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

theorem normalMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) =
      ∫ x : Cover, characteristic E (quotientMap x) * divergence F x := by
  let G := latticePeriodize F
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := latticePeriodize_contDiff hF hc
  have hGp : ∀ n x, G (x + latticeVector n) = G x := latticePeriodize_periodic F
  obtain ⟨M, hM, hb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1)
    (fun x ↦ (hb x).trans (by linarith : M ≤ M + 1))
  have he (z : NormalBundle) : G z.1 = F z.1 :=
    (latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)).eq_of_nhds
  change (∫ z, ⟪(z.2 : Cover), G z.1⟫ ∂(μ : Measure NormalBundle)) = _ at hflux
  simp_rw [he] at hflux
  have hdiv : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence G x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
      with x hx
    have hd := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx.1 i).1, (hx.1 i).2.le⟩)).fderiv_eq (𝕜 := ℝ)
    simp only [divergence, G, hd]
  rw [hdiv] at hflux
  rw [hflux, ← integral_indicator (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · by_cases he : quotientMap x ∈ E <;> simp [characteristic, hx, he]
  · have hd : divergence F x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      apply hx
      exact fun i ↦ ⟨(hs hh i).1.le, (hs hh i).2⟩
    simp [hx, hd]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma scaledTestField_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a : Cover) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledTestField a r F) :=
  (hF.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul r

lemma fderiv_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    fderiv ℝ (scaledTestField a r F) x = fderiv ℝ F (r⁻¹ • (x - a)) := by
  have hψ : HasFDerivAt (fun y : Cover ↦ r⁻¹ • (y - a))
      (r⁻¹ • (ContinuousLinearMap.id ℝ Cover)) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul r⁻¹
  have h := (((hF _).hasFDerivAt).comp x hψ).const_smul r
  change HasFDerivAt (scaledTestField a r F) _ x at h
  rw [h.fderiv]
  ext v
  simp [smul_smul, hr]

lemma divergence_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    divergence (scaledTestField a r F) x = divergence F (r⁻¹ • (x - a)) := by
  simp only [divergence, fderiv_scaledTestField hF a x hr]

lemma scaledTestField_tsupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledTestField a r F) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hFx : F (r⁻¹ • (x - a)) ≠ 0 := by
    intro h
    exact hx (by simp [scaledTestField, h])
  have hb := hs (subset_closure hFx)
  have hb' : ‖x - a‖ / r ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul] using hb
  exact (div_le_iff₀ hr).mp hb' |>.trans_eq (one_mul r)

lemma scaledTestField_hasCompactSupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledTestField a r F) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (scaledTestField_tsupport hs a hr)

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

theorem normalMeasure_scaled_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 2 =
      ∫ x : Cover, characteristic E (quotientMap (r • x + a)) * divergence F x := by
  have hflux := normalMeasure_local_flux hE hμ (scaledTestField_contDiff hF a r)
    (scaledTestField_hasCompactSupport hs a hr) ((scaledTestField_tsupport hs a hr).trans hc)
  simp only [scaledTestField, inner_smul_right, integral_const_mul] at hflux
  have hscale := integral_cover_affine_scaling
    (fun x ↦ characteristic E (quotientMap x) * divergence (scaledTestField a r F) x) a hr
  have hdiv (x : Cover) : divergence (scaledTestField a r F) (r • x + a) = divergence F x := by
    rw [divergence_scaledTestField (hF.differentiable (by simp)) a _ hr.ne']
    simp [hr.ne']
  simp_rw [hdiv] at hscale
  rw [hscale] at hflux
  calc
    _ = (r * ∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 3 := by
      field_simp
    _ = _ := by rw [hflux]; field_simp

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

theorem totallyBounded_blowupCharacteristic {ι : Type*} {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) (r : ι → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 0 < R)
    (hc : ∀ i, Metric.ball c (r i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : ∀ i, (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (r i*((R+1)+2))) ≤ A*(r i*((R+1)+2))^2) :
    TotallyBounded (range fun i ↦ boundedFunctionL1
      (volume.restrict (Metric.closedBall (0 : Cover) R)) (blowupCharacteristic E c (r i))
      (measurable_blowupCharacteristic hE c (r i)) (blowupCharacteristic_bound E c (r i))) := by
  apply totallyBounded_local_translation (η := volume) (isCompact_closedBall _ _)
    (fun i ↦ blowupCharacteristic E c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE c (r i))
    (fun i ↦ blowupCharacteristic_bound E c (r i))
    (A := A*((R+1)+2)^2) (ε₀ := 1) (by positivity) (by norm_num)
  intro i y hy
  have htrans := blowupCharacteristic_translation_density hE hμ c (hr i)
    (by linarith : 0 ≤ R+1) (hc i) hA (harea i) y hy
  apply le_trans _ htrans
  apply setIntegral_mono_set _ (ae_of_all _ fun _ ↦ abs_nonneg _)
    (ae_of_all _ fun _ hx ↦ Metric.closedBall_subset_ball (by linarith : R < R+1) hx)
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Cover) (R+1))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hf := measurable_blowupCharacteristic hE c (r i)
  have hbound := blowupCharacteristic_bound E c (r i)
  apply Integrable.of_bound (μ := volume.restrict (Metric.ball (0 : Cover) (R+1)))
    (((hf.comp (measurable_id.sub_const y)).sub hf).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs,abs_abs,Function.comp_apply,id_eq,Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith [hbound (x-y),hbound x])

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_blowupNormalMap (c : Cover) (r : ℝ) :
    Continuous (blowupNormalMap c r) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

lemma blowupNormalMeasure_mass (μ : FiniteMeasure NormalBundle) (c : Cover) (r R : ℝ) :
    ((blowupNormalMeasure μ c r R).mass : ℝ) = r⁻¹^2*cellBallMass μ c (r*R) := by
  change (((Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (blowupNormalMap c r)) univ) : ℝ) = _
  rw [FiniteMeasure.smul_apply,FiniteMeasure.map_apply _
    (continuous_blowupNormalMap c r).measurable MeasurableSet.univ]
  rw [Set.preimage_univ,FiniteMeasure.restrict_apply _ _ MeasurableSet.univ,univ_inter]
  change (Real.toNNReal (r⁻¹^2) : ℝ) *
    (((μ : Measure NormalBundle) {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma blowupNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : NormalBundle) :
    (blowupNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [blowupNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

lemma blowupNormalMeasure_supported (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    blowupNormalMeasure μ c r R ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 := by
  have hm : MeasurableSet ((Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere))ᶜ) :=
    (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ).compl
  have he : (blowupNormalMap c r ⁻¹' ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ)) ∩
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨Metric.ball_subset_closedBall ((blowupNormalMap_mem c hr R z).mpr hz.2),mem_univ _⟩
  unfold blowupNormalMeasure
  rw [FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (continuous_blowupNormalMap c r).measurable hm,
    FiniteMeasure.restrict_apply _ _ (hm.preimage (continuous_blowupNormalMap c r).measurable),he]
  simp [FiniteMeasure.coeFn_def]

theorem blowupNormalMeasure_cluster {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, cellBallMass μ c (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ blowupNormalMeasure μ c (r i) R) := by
  have hm (i) : (blowupNormalMeasure μ c (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,blowupNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ blowupNormalMeasure μ c (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,blowupNormalMeasure_supported μ c (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma integral_blowupNormalMeasure (μ : FiniteMeasure NormalBundle) (c : Cover)
    (r R : ℝ) {g : BlowupNormalBundle → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)},
        g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [blowupNormalMeasure,FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure,
    FiniteMeasure.toMeasure_map,integral_map
      (continuous_blowupNormalMap c r).measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  change (Real.toNNReal (r⁻¹^2) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma integral_blowup_test (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r R : ℝ} (hr : 0 < r) {g : BlowupNormalBundle → ℝ} (hg : Continuous g)
    (hzero : ∀ z, z.1 ∉ Metric.ball (0 : Cover) R → g z = 0) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z, g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [integral_blowupNormalMeasure μ c r R hg]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero _ (by rwa [blowupNormalMap_mem c hr R z])

lemma tangentialDivergence_scaledTestField {F : Cover → Cover}
    (hF : Differentiable ℝ F) (c x n : Cover) {r : ℝ} (hr : r ≠ 0) :
    tangentialDivergence (scaledTestField c r F) x n =
      tangentialDivergence F (r⁻¹ • (x-c)) n := by
  simp only [tangentialDivergence,divergence_scaledTestField hF c x hr,
    fderiv_scaledTestField hF c x hr]

theorem weakCMC_blowup_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (c : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall c r ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2
      ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      (r*H) * ∫ z, ⟪(z.2 : Cover),F z.1⟫
        ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle) := by
  have ht (z : BlowupNormalBundle) (hz : z.1 ∉ Metric.ball (0 : Cover) R) :
      z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
  rw [integral_blowup_test μ c hr (continuous_blowupTangentTest hF)
      (fun z hz ↦ tangentialDivergence_zero_of_notMem_tsupport (ht z hz) z.2),
    integral_blowup_test μ c hr (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport (ht z hz)])]
  have hid := weakCMC_local_identity hμ hH (scaledTestField_contDiff hF c r)
    (scaledTestField_hasCompactSupport hs c hr) ((scaledTestField_tsupport hs c hr).trans hc)
  simp only [tangentialDivergence_scaledTestField (hF.differentiable (by simp)) c _ _ hr.ne',
    scaledTestField,inner_smul_right,integral_const_mul] at hid
  change r⁻¹^2*(∫ z, tangentialDivergence F (r⁻¹ • ((z.1 : Cover)-c)) z.2
    ∂(μ : Measure NormalBundle)) = _
  rw [hid]
  simp only [blowupNormalMap]
  ring

theorem weakCMC_blowup_limit_stationary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall c (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupTangentTest hF hFs)
  have hf := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupFluxTest hF.continuous hFs)
  have hh := (hrlim.mul_const H).mul hf
  simp only [zero_mul] at hh
  have he (i) := weakCMC_blowup_identity hμ hH hF hs c (hr i) hR (hc i)
  exact tendsto_nhds_unique ht (hh.congr (fun i ↦ (he i).symm))

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_blowup_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : Cover) {d : ℝ} (hd : 0 < d)
    (hc : Metric.ball c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ F : Set Cover, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E c (r (φ i)) x-F.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Cover) R),
        Tendsto (fun i ↦ blowupCharacteristic E c (r (φ i)) x) atTop
          (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  have hsmall : 0 < min (d/(R+1)) (S/((R+1)+2)) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsb (i) : s i < min (d/(R+1)) (S/((R+1)+2)) := hk _ (by omega)
  have hchart (i) : Metric.ball c (s i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.ball_subset_ball _).trans hc
    exact ((lt_div_iff₀ (by linarith : 0 < R+1)).mp
      ((hsb i).trans_le (min_le_left _ _))).le
  have hb (i) : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (s i*((R+1)+2))) ≤ A*(s i*((R+1)+2))^2 := by
    apply harea μ hμ _ _ (by have hh := hs i; positivity)
    exact ((lt_div_iff₀ (by linarith : 0 < (R+1)+2)).mp
      ((hsb i).trans_le (min_le_right _ _))).le
  have ht := totallyBounded_blowupCharacteristic hE hμ c s hs hR hchart hA.le hb
  obtain ⟨F,hF,φ,hφ,hconv,hae⟩ := exists_cover_indicator_limit
    (fun i ↦ blowupCharacteristic E c (s i))
    (fun i ↦ measurable_blowupCharacteristic hE c (s i))
    (fun i ↦ blowupCharacteristic_bound E c (s i))
    (fun i x ↦ characteristic_dichotomy E (quotientMap (c+s i • x))) ht
  refine ⟨F,hF,fun i ↦ φ i+k,fun i j hij ↦ Nat.add_lt_add_right (hφ hij) k,?_,hae⟩
  exact boundedFunctionL1_integral_tendsto
    (fun i ↦ blowupCharacteristic E c (s (φ i)))
    (fun i ↦ measurable_blowupCharacteristic hE c (s (φ i)))
    (fun i ↦ blowupCharacteristic_bound E c (s (φ i)))
    (measurable_const.indicator hF) (cover_indicator_bound F) hconv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma localL1_weighted_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    {l : Filter ℕ} (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) l (𝓝 0))
    (k : Cover →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, g i x*k x ∂η) l (𝓝 (∫ x, f x*k x ∂η)) := by
  have hi (i) : Integrable (fun x ↦ g i x*k x) η :=
    Integrable.of_bound ((hg i).mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hgb i x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hfi : Integrable (fun x ↦ f x*k x) η :=
    Integrable.of_bound (hf.mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hfb x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hdiff (i) : Integrable (fun x ↦ |g i x-f x|) η :=
    ((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs
  have hbound (i) : ‖(∫ x, g i x*k x ∂η)-(∫ x, f x*k x ∂η)‖ ≤
      ‖k‖ * ∫ x, |g i x-f x| ∂η := by
    rw [← integral_sub (hi i) hfi,← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono ((hi i).sub hfi).norm ((hdiff i).const_mul ‖k‖)
    intro x
    change ‖g i x*k x-f x*k x‖ ≤ ‖k‖*|g i x-f x|
    rw [← sub_mul,Real.norm_eq_abs,abs_mul]
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (abs_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i ↦ norm_nonneg _) hbound (by simpa using hlim.const_mul ‖k‖)

theorem blowup_limit_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall c (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {A : Set Cover} (hA : MeasurableSet A)
    (hAconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E c (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ x in A, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hd : HasCompactSupport (divergence F) := hFs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  let k : Cover →ᵇ ℝ := ofCompactSupport _ (continuous_divergence hF) hd
  have hstri := localL1_weighted_integral_tendsto
    (fun i ↦ blowupCharacteristic E c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE c (r i))
    (fun i ↦ blowupCharacteristic_bound E c (r i))
    (measurable_const.indicator hA)
    (fun x ↦ by by_cases hx : x ∈ A <;> simp [hx]) hAconv k
  have hzero (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) R) : divergence F x = 0 :=
    divergence_of_notMem_tsupport (fun hh ↦ hx (Metric.closedBall_subset_closedBall hR.le (hs hh)))
  have heg (i) : (∫ x in Metric.closedBall (0 : Cover) R, blowupCharacteristic E c (r i) x*k x) =
      ∫ x, blowupCharacteristic E c (r i) x*divergence F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hzero x hx,mul_zero])
  have hef : (∫ x in Metric.closedBall (0 : Cover) R, A.indicator (fun _ ↦ (1 : ℝ)) x*k x) =
      ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hzero x hx,mul_zero])]
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence F x) = _
    simp only [← indicator_mul_left,one_mul]
    exact integral_indicator hA
  simp_rw [heg] at hstri
  rw [hef] at hstri
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (blowupFluxTest hF.continuous hFs)
  have he (i) : (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(blowupNormalMeasure μ c (r i) R : Measure BlowupNormalBundle)) =
      ∫ x, blowupCharacteristic E c (r i) x*divergence F x := by
    rw [integral_blowup_test μ c (hr i) (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by
        have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
        simp [image_eq_zero_of_notMem_tsupport hn])]
    change (r i)⁻¹^2*(∫ z, ⟪(z.2 : Cover),F ((r i)⁻¹ • ((z.1 : Cover)-c))⟫ ∂(μ : Measure NormalBundle)) = _
    rw [show (r i)⁻¹^2 = ((r i)^2)⁻¹ by ring]
    rw [← div_eq_inv_mul,normalMeasure_scaled_flux hE hμ hF hs c (hr i) (hc i)]
    simp only [blowupCharacteristic,add_comm c]
  exact tendsto_nhds_unique (hweak.congr fun i ↦ he i) hstri

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma finiteMeasure_real_closed_lower {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]
    {l : Filter ℕ} [NeBot l] {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {s t : Set X} (ht : IsClosed t) (hst : s ⊆ t)
    {b : ℝ} (hb : Tendsto (fun i ↦ (μ i : Measure X).real s) l (𝓝 b)) :
    b ≤ (ν : Measure X).real t := by
  have hbpos : 0 ≤ b := ge_of_tendsto hb (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  have heq (i) : ENNReal.ofReal ((μ i : Measure X).real s) = (μ i : Measure X) s :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  change Tendsto (fun i ↦ ENNReal.ofReal ((μ i : Measure X).real s)) l (𝓝 (ENNReal.ofReal b)) at he
  simp_rw [heq] at he
  have hle : ENNReal.ofReal b ≤ (ν : Measure X) t := by
    rw [← he.limsup_eq]
    exact (limsup_le_limsup (Eventually.of_forall fun i ↦ measure_mono hst)).trans
      (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim ht)
  simpa only [ENNReal.toReal_ofReal hbpos,Measure.real] using ENNReal.toReal_mono (measure_ne_top _ _) hle

lemma finiteMeasure_real_open_upper {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]
    {l : Filter ℕ} [NeBot l] {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {s : Set X} (hs : IsOpen s)
    {b : ℝ} (hb : Tendsto (fun i ↦ (μ i : Measure X).real s) l (𝓝 b)) :
    (ν : Measure X).real s ≤ b := by
  have hm : Tendsto (fun i ↦ (μ i : Measure X).real univ) l
      (𝓝 ((ν : Measure X).real univ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (FiniteMeasure.continuous_mass.tendsto ν |>.comp hlim)
  have hh := finiteMeasure_real_closed_lower hlim hs.isClosed_compl (Subset.refl sᶜ)
    (show Tendsto (fun i ↦ (μ i : Measure X).real sᶜ) l
      (𝓝 ((ν : Measure X).real univ-b)) by
      simp_rw [measureReal_compl hs.measurableSet]
      exact hm.sub hb)
  rw [measureReal_compl hs.measurableSet] at hh
  linarith

lemma blowupNormalMeasure_ball (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r ρ R : ℝ} (hr : 0 < r) (hρ : ρ ≤ R) :
    (blowupNormalMeasure μ c r R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = r⁻¹^2*cellBallMass μ c (r*ρ) := by
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} :=
    Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have he : blowupNormalMap c r ⁻¹' {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} ∩
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} =
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*ρ)} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,blowupNormalMap_mem c hr ρ]
    exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hρ hr.le) hz⟩⟩
  unfold blowupNormalMeasure
  rw [FiniteMeasure.toMeasure_smul]
  change ((_ : Measure BlowupNormalBundle) _).toReal = _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,FiniteMeasure.toMeasure_map,
    Measure.map_apply (continuous_blowupNormalMap c r).measurable hm,
    FiniteMeasure.restrict_measure_eq,Measure.restrict_apply
      (hm.preimage (continuous_blowupNormalMap c r).measurable),he]
  simp only [ENNReal.coe_toReal,Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma blowupNormalMeasure_ball_tendsto {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ cellBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    Tendsto (fun i ↦ (blowupNormalMeasure μ c (r i) R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ}) l (𝓝 (θ*ρ^2)) := by
  have ht : Tendsto (fun i ↦ r i*ρ) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const ρ,
      Eventually.of_forall fun i ↦ mul_pos (hr i) hρ⟩
  have hh := (hθ.comp ht).mul_const (ρ^2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [blowupNormalMeasure_ball μ c (hr i) hρR]
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',hρ.ne']

theorem blowup_limit_ball_mass {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ cellBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {R : ℝ} {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2 := by
  apply le_antisymm
  · exact finiteMeasure_real_open_upper hν (Metric.isOpen_ball.preimage continuous_fst)
      (blowupNormalMeasure_ball_tendsto c r hr hrlim hθ hρ hρR.le)
  · have hlow (s : ℝ) (hs : s ∈ Ioo 0 ρ) : θ*s^2 ≤
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} := by
      apply (finiteMeasure_real_closed_lower hν
        (Metric.isClosed_closedBall.preimage continuous_fst)
        (show {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) s} ⊆
          {z | z.1 ∈ Metric.closedBall (0 : Cover) s} from fun _ hz ↦ Metric.ball_subset_closedBall hz)
        (blowupNormalMeasure_ball_tendsto c r hr hrlim hθ hs.1 (hs.2.trans hρR).le)).trans
      exact measureReal_mono (fun _ hz ↦ Metric.closedBall_subset_ball hs.2 hz)
    have hh : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[<] ρ) (𝓝 (θ*ρ^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hρ)] with s hs hs0
    exact hlow s ⟨hs0,hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma normalBall_measure_of_real {ν : FiniteMeasure BlowupNormalBundle} {θ ρ : ℝ}
    (h : (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = ENNReal.ofReal (θ*ρ^2) := by
  rw [← h,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma norm_sq_lt_iff {x : Cover} {t : ℝ} (ht : 0 < t) :
    ‖x‖^2 < t ↔ x ∈ Metric.ball (0 : Cover) (Real.sqrt t) := by
  rw [Metric.mem_ball,dist_zero_right]
  have hs := Real.sq_sqrt ht.le
  have hp := Real.sqrt_pos.mpr ht
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

theorem squaredRadius_distribution {ν : FiniteMeasure BlowupNormalBundle} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    Measure.map (fun z : BlowupNormalBundle ↦ ‖z.1‖^2)
      ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ Metric.ball (0 : Cover) 1}) =
      ENNReal.ofReal θ • volume.restrict (Ioo (0 : ℝ) 1) := by
  have hmap : Measurable (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) := measurable_fst.norm.pow_const _
  have hb1 := normalBall_measure_of_real (hm 1 (by norm_num) le_rfl)
  simp only [one_pow,mul_one] at hb1
  apply ext_of_generate_finite (range (Iio : ℝ → Set ℝ))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio
  · rintro _ ⟨t,rfl⟩
    rw [Measure.map_apply hmap measurableSet_Iio,Measure.restrict_apply
      (measurableSet_Iio.preimage hmap),Measure.smul_apply,smul_eq_mul,
      Measure.restrict_apply measurableSet_Iio]
    by_cases ht : t ≤ 0
    · have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
          {z | z.1 ∈ Metric.ball (0 : Cover) 1} = ∅ := by
        ext z
        simp only [mem_inter_iff,mem_preimage,mem_Iio,mem_empty_iff_false,iff_false,not_and]
        intro hz
        exact False.elim ((not_lt_of_ge (le_trans ht (sq_nonneg _))) hz)
      have hI : Iio t ∩ Ioo (0 : ℝ) 1 = ∅ := by
        ext x
        simp only [mem_inter_iff,mem_Iio,mem_Ioo,mem_empty_iff_false,iff_false,not_and]
        intro hx hx0 _
        linarith
      rw [he,hI,measure_empty,measure_empty,mul_zero]
    · have ht0 := lt_of_not_ge ht
      by_cases ht1 : 1 ≤ t
      · have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
            {z | z.1 ∈ Metric.ball (0 : Cover) 1} = {z | z.1 ∈ Metric.ball (0 : Cover) 1} := by
          apply inter_eq_right.mpr
          intro z hz
          have hz' : ‖z.1‖ < 1 := by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hz
          change ‖z.1‖^2 < t
          nlinarith [norm_nonneg z.1]
        have hI : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 1 := inter_eq_right.mpr (fun _ hx ↦ hx.2.trans_le ht1)
        rw [he,hI,hb1,Real.volume_Ioo]
        norm_num
      · have htlt := lt_of_not_ge ht1
        have hs : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht0.le,Real.sqrt_nonneg t]
        have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
            {z | z.1 ∈ Metric.ball (0 : Cover) 1} =
            {z | z.1 ∈ Metric.ball (0 : Cover) (Real.sqrt t)} := by
          ext z
          change (‖z.1‖^2 < t ∧ z.1 ∈ Metric.ball (0 : Cover) 1) ↔ _
          rw [norm_sq_lt_iff ht0]
          exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball hs hz⟩⟩
        have hI : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 t := by ext x; simp only [mem_inter_iff,mem_Iio,mem_Ioo]; grind
        rw [he,hI,normalBall_measure_of_real (hm _ (Real.sqrt_pos.mpr ht0) hs),
          Real.sq_sqrt ht0.le,Real.volume_Ioo,sub_zero,ENNReal.ofReal_mul hθ]
  · rw [Measure.map_apply hmap MeasurableSet.univ,preimage_univ,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter,hb1,
      Real.volume_Ioo]
    norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Ioo 0 1) :
    0 < deriv Real.smoothTransition t := by
  have he (x : ℝ) : HasDerivAt expNegInvGlue
      (x⁻¹^2*expNegInvGlue x) x := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x
  have hd := (he t).div ((he t).add ((he (1-t)).comp t ((hasDerivAt_id t).const_sub 1)))
    (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition _ t at hd
  rw [hd.deriv]
  have hu := expNegInvGlue.pos_of_pos ht.1
  have hv := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have hu' : 0 < t⁻¹^2*expNegInvGlue t := mul_pos (sq_pos_of_pos (inv_pos.mpr ht.1)) hu
  have hv' : 0 < (1-t)⁻¹^2*expNegInvGlue (1-t) :=
    mul_pos (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr ht.2))) hv
  apply div_pos _ (sq_pos_of_pos (Real.smoothTransition.pos_denom t))
  simp only [Pi.add_apply,Function.comp_apply] at *
  nlinarith [mul_pos hu' hv,mul_pos hu hv']

lemma continuous_radialBalance : Continuous radialBalance :=
  (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)).sub
    (continuous_id.mul (((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).comp
      (continuous_const.sub continuous_id)))

lemma integral_radialBalance : (∫ t : ℝ in Ioo 0 1, radialBalance t) = 0 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ s*Real.smoothTransition (1-s)) (radialBalance t) t := by
    have hh := (hasDerivAt_id t).mul
      (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (1-t)).hasDerivAt.comp t
        ((hasDerivAt_id t).const_sub 1))
    exact hh.congr_deriv (by dsimp [radialBalance]; ring)
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (continuous_radialBalance.intervalIntegrable 0 1)]
  simp

lemma radialBalance_zero {t : ℝ} (ht : 1 ≤ t) : radialBalance t = 0 := by
  rw [radialBalance,Real.smoothTransition.zero_of_nonpos (by linarith),
    smoothTransition_deriv_zero_of_nonpos (by linarith),mul_zero,sub_zero]

lemma quadraticMass_radialBalance {ν : FiniteMeasure BlowupNormalBundle} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    (∫ z : BlowupNormalBundle, radialBalance (‖z.1‖^2) ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hmap : Measurable (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) := measurable_fst.norm.pow_const _
  have he := integral_map (μ := (ν : Measure BlowupNormalBundle).restrict
    {z | z.1 ∈ Metric.ball (0 : Cover) 1}) hmap.aemeasurable
      continuous_radialBalance.measurable.aestronglyMeasurable
  rw [squaredRadius_distribution hθ hm,integral_smul_measure,integral_radialBalance,smul_zero] at he
  have hz : ∀ z : BlowupNormalBundle, z ∉ {z | z.1 ∈ Metric.ball (0 : Cover) 1} →
      radialBalance (‖z.1‖^2) = 0 := by
    intro z hz
    apply radialBalance_zero
    have hh : 1 ≤ ‖z.1‖ := by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right,not_lt] using hz
    nlinarith
  have hg := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (ν : Measure BlowupNormalBundle)) hz
  exact hg.symm.trans he.symm

lemma integrable_radialTangency (ν : FiniteMeasure BlowupNormalBundle) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2)
      (ν : Measure BlowupNormalBundle) := by
  let g : BlowupNormalBundle → ℝ := fun z ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2
  have hgcont : Continuous g := by
    apply ((continuous_radialDensitySlope 0 1 1).comp continuous_fst).mul
    exact ((continuous_subtype_val.comp continuous_snd).inner continuous_fst).pow 2
  have hgs : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : Cover) 1 |>.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
    intro z hz
    refine ⟨?_,mem_univ _⟩
    by_contra hh
    apply hz
    have hb' : 1 < ‖z.1‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hh
    have hb : 1 ≤ ‖z.1-(0 : Cover)‖ := by simpa only [sub_zero] using hb'.le
    simp [g,radialDensitySlope_zero (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) hb]
  exact hgcont.integrable_of_hasCompactSupport (μ := (ν : Measure BlowupNormalBundle)) hgs

lemma integrable_radialBalanceNorm (ν : FiniteMeasure BlowupNormalBundle) :
    Integrable (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2))
      (ν : Measure BlowupNormalBundle) := by
  have hbcont : Continuous (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2)) :=
    continuous_radialBalance.comp (continuous_fst.norm.pow 2)
  have hbs : HasCompactSupport (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2)) := by
    apply (isCompact_closedBall (0 : Cover) 1 |>.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
    intro z hz
    refine ⟨?_,mem_univ _⟩
    by_contra hh
    apply hz
    apply radialBalance_zero
    have hb : 1 < ‖z.1‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hh
    nlinarith
  exact hbcont.integrable_of_hasCompactSupport (μ := (ν : Measure BlowupNormalBundle)) hbs

lemma tangentialDivergence_radialBalance (z : BlowupNormalBundle) :
    tangentialDivergence (radialDensityField 0 1 1) z.1 z.2 =
      2*radialBalance (‖z.1‖^2)+2*(radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2) := by
  rw [tangentialDivergence_radialDensityField z.2.property]
  simp only [radialBalance,radialDensityWeight,radialDensitySlope,sublevelCutoff,one_pow,sub_zero,div_one]
  ring

theorem stationary_quadraticMass_radial_tangent {ν : FiniteMeasure BlowupNormalBundle}
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2)
    (hstat : ∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
      ⟪(z.2 : Cover),z.1⟫ = 0 := by
  have hs := hstat (radialDensityField 0 1 1) (radialDensityField_contDiff 0 1 1)
    (radialDensityField_tsupport (by norm_num) (by norm_num))
  let g : BlowupNormalBundle → ℝ := fun z ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2
  have hgi : Integrable g (ν : Measure BlowupNormalBundle) := integrable_radialTangency ν
  have hbi := integrable_radialBalanceNorm ν
  have he (z : BlowupNormalBundle) : tangentialDivergence (radialDensityField 0 1 1) z.1 z.2 =
      2*radialBalance (‖z.1‖^2)+2*g z := tangentialDivergence_radialBalance z
  simp_rw [he] at hs
  rw [integral_add (hbi.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul,
    quadraticMass_radialBalance hθ hm] at hs
  have hzero : (∫ z, g z ∂(ν : Measure BlowupNormalBundle)) = 0 := by linarith
  have hgn : ∀ z, 0 ≤ g z := fun z ↦
    mul_nonneg (radialDensitySlope_nonneg (0 : Cover) 1 (by norm_num : (0 : ℝ) < 1) z.1) (sq_nonneg _)
  have hae : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), g z = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all (ν : Measure BlowupNormalBundle) hgn) hgi).mp hzero
  filter_upwards [hae] with z hz hzball
  by_cases hx : z.1 = 0
  · simp [hx]
  · have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hx
    have hb : ‖z.1‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hzball
    have hp : 0 < radialDensitySlope 0 1 1 z.1 := by
      simp only [radialDensitySlope,one_pow,sub_zero,div_one]
      exact smoothTransition_deriv_pos ⟨by nlinarith,by nlinarith⟩
    have hsq : ⟪(z.2 : Cover),z.1⟫^2 = 0 := (mul_eq_zero.mp hz).resolve_left hp.ne'
    exact sq_eq_zero_iff.mp hsq

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

theorem isMinimizerAt_paired_blowup_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : Cover) {d : ℝ} (hd : 0 < d)
    (hc : Metric.closedBall c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ) (U : Ultrafilter ℕ),
      MeasurableSet A ∧ 0 ≤ θ ∧ StrictMono φ ∧ (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E c (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ c (r (φ i)) 2) U (𝓝 ν) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
          ∫ x in A, divergence F x) ∧
      (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
        ⟪(z.2 : Cover),z.1⟫ = 0) := by
  obtain ⟨S,B,hS,hB,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨θ,hθ,hdens⟩ := exists_density_of_cmc_monotone hd
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH c hc)
  have hsmall : 0 < min (d/2) (S/2) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsbound (i) : s i < min (d/2) (S/2) := hk _ (by omega)
  have hslim : Tendsto s atTop (𝓝 0) := hrlim.comp (tendsto_add_atTop_nat k)
  obtain ⟨A,hA,ψ,hψ,hconv,_⟩ := isMinimizerAt_blowup_limit hV hE hmin c hd
    (Metric.ball_subset_closedBall.trans hc) s hs hslim (by norm_num : (0 : ℝ) < 2)
  have hchart (i) : Metric.closedBall c (s (ψ i)*2) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.closedBall_subset_closedBall _).trans hc
    have hh := (hsbound (ψ i)).trans_le (min_le_left _ _)
    linarith
  have hmass (i) : cellBallMass μ c (s (ψ i)*2) ≤ (B*4)*(s (ψ i))^2 := by
    rw [cellBallMass_eq_spatialNormalMeasure μ c _ (Metric.ball_subset_closedBall.trans (hchart i))]
    have hh := harea μ hμ (quotientMap c) (s (ψ i)*2) (mul_pos (hs _) (by norm_num)) (by
      have hh := (hsbound (ψ i)).trans_le (min_le_right _ _)
      linarith)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨ν,_,_,hcl⟩ := blowupNormalMeasure_cluster c (fun i ↦ s (ψ i))
    (fun i ↦ hs _) (by positivity : 0 ≤ B*4) hmass
  obtain ⟨U,hU,hν⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hrl : Tendsto (fun i ↦ s (ψ i)) (U : Filter ℕ) (𝓝 0) :=
    (hslim.comp hψ.tendsto_atTop).mono_left hU
  have hcm (i) : Metric.closedBall c (s (ψ i)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.closedBall_subset_closedBall (by have hh := hs (ψ i); linarith)).trans (hchart i)
  have hm (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 2) :=
    blowup_limit_ball_mass c (fun i ↦ s (ψ i)) (fun i ↦ hs _) hrl hdens hν hρ hρ2
  have hstat (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hFs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    weakCMC_blowup_limit_stationary hμ hH c (fun i ↦ s (ψ i)) (fun i ↦ hs _)
      (by norm_num : (1 : ℝ) < 2) hcm hrl hν hF hFs
  refine ⟨A,ν,θ,fun i ↦ ψ i+k,U,hA,hθ,fun i j hij ↦ Nat.add_lt_add_right (hψ hij) k,
    hU,hconv,hν,hm,?_,stationary_quadraticMass_radial_tangent hθ (fun ρ hρ hρ1 ↦ hm ρ hρ (by linarith)) hstat⟩
  intro F hF hFs
  exact ⟨hstat F hF hFs,blowup_limit_flux hE hμ c (fun i ↦ s (ψ i)) (fun i ↦ hs _)
    (by norm_num : (1 : ℝ) < 2) hcm hν hA (hconv.mono_left hU) hF hFs⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_paired_blowup_oai := @OAI.CubicTorus.isMinimizerAt_paired_blowup_oai
