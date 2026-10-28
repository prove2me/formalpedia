-- Prove2me | solution 1 for OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:49:27.848835+00:00
-- url     : https://prove2.me/submissions/c6550eb3-a26c-4cfd-b97c-30d2c163c5b7

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

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
open scoped Topology Convolution RealInnerProductSpace

lemma characteristic_nonneg (E : Set Torus) (x : Torus) : 0 ≤ characteristic E x := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_characteristic_mul {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) {g : Cover → ℝ}
    (hg : IntegrableOn g fundamentalCube) :
    IntegrableOn (fun x ↦ characteristic E (quotientMap x) * g x) fundamentalCube := by
  simp_rw [characteristic_mul]
  exact hg.indicator₀ (hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving)

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
open scoped RealInnerProductSpace

lemma normalTest_le_one {F : Cover → Cover} (hF : AdmissibleField F) (z : NormalBundle) :
    normalTest F hF.1.continuous z ≤ 1 := by
  calc
    _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [z.2.property, one_mul] using hF.2.2 z.1

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
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

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma monotone_exists_deriv_le {m : ℝ → ℝ} (hm : Monotone m) {a b M : ℝ}
    (hab : a < b) (hbound : m b - m a < M * (b - a)) :
    ∃ t ∈ Ioo a b, DifferentiableAt ℝ m t ∧ deriv m t ≤ M := by
  by_contra! hn
  have haeb : ∀ᵐ x ∂volume.restrict (Icc a b), M ≤ deriv m x := by
    filter_upwards [ae_restrict_of_ae hm.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff]),
      ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff])] with x hx hxab hxa hxb
    exact le_of_lt (hn x ⟨hxab.1.lt_of_ne hxa.symm, hxab.2.lt_of_ne hxb⟩ hx)
  have hi := intervalIntegral.integral_mono_ae_restrict hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ M) volume a b)
    ((hm.monotoneOn _).intervalIntegrable_deriv) haeb
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hu := (hm.monotoneOn _).intervalIntegral_deriv_mem_uIcc (a := a) (b := b)
  rw [uIcc_of_le (sub_nonneg.mpr (hm hab.le))] at hu
  linarith [hu.2]

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

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

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

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

lemma radialDensityWeight_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityWeight a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (radialDensityWeight_zero hr hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hh)))

lemma radialDensityWeight_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityWeight a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityWeight_tsupport hr hε)

lemma radialHeightCutoff_one {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a r) : radialHeightCutoff a r x = 1 := by
  have hnorm : ‖x - a‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by positivity : 0 < 3 * r ^ 2)).mpr
  nlinarith [norm_nonneg (x - a)]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
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
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

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
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma characteristic_symmDiff_abs (E F : Set Torus) (x : Torus) :
    |characteristic F x - characteristic E x| = characteristic (E ∆ F) x := by
  classical
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;>
    simp [characteristic, Set.mem_symmDiff, he, hf]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma measurableSet_gluedRegion {E F B : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hB : MeasurableSet B) :
    MeasurableSet (gluedRegion E F B) := (hE.diff hB).union (hF.inter hB)

lemma characteristic_gluedRegion (E F B : Set Torus) (x : Torus) :
    characteristic (gluedRegion E F B) x =
      (1 - characteristic B x) * characteristic E x + characteristic B x * characteristic F x := by
  classical
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> by_cases hb : x ∈ B <;>
    simp [characteristic, gluedRegion, he, hf, hb]

lemma cutoff_gluing_flux_tendsto {E F B : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hB : MeasurableSet B)
    {w : ℕ → Cover → ℝ} (hw : ∀ i, Continuous (w i))
    (hb : ∀ i x, w i x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun i ↦ w i x) atTop (𝓝 (characteristic B (quotientMap x))))
    {X : Cover → Cover} (hX : AdmissibleField X) :
    Tendsto (fun i ↦ ∫ x in fundamentalCube,
      ((1 - w i x) * characteristic E (quotientMap x) + w i x * characteristic F (quotientMap x)) *
        divergence X x) atTop
      (𝓝 (∫ x in fundamentalCube ∩ quotientMap ⁻¹' gluedRegion E F B, divergence X x)) := by
  have hg := measurableSet_gluedRegion hE hF hB
  have he : Measurable (fun x : Cover ↦ characteristic E (quotientMap x)) :=
    (measurable_characteristic hE).comp measurable_quotientMap
  have hf : Measurable (fun x : Cover ↦ characteristic F (quotientMap x)) :=
    (measurable_characteristic hF).comp measurable_quotientMap
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict fundamentalCube) (bound := fun x ↦ |divergence X x|)
    (F := fun i x ↦ ((1 - w i x) * characteristic E (quotientMap x) +
      w i x * characteristic F (quotientMap x)) * divergence X x)
    (f := fun x ↦ characteristic (gluedRegion E F B) (quotientMap x) * divergence X x)
    (fun i ↦ ((((measurable_const.sub (hw i).measurable).mul he).add
      ((hw i).measurable.mul hf)).mul (continuous_divergence hX.1).measurable).aestronglyMeasurable)
    (integrableOn_divergence hX.1).abs (fun i ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ ?_)
  · simpa only [characteristic_mul, lift_indicator_integral hg.nullMeasurableSet] using hlim
  · rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    have he0 := characteristic_nonneg E (quotientMap x)
    have hf0 := characteristic_nonneg F (quotientMap x)
    have he1 := (le_abs_self _).trans (characteristic_bound E (quotientMap x))
    have hf1 := (le_abs_self _).trans (characteristic_bound F (quotientMap x))
    have hw0 := (hb i x).1
    have hw1 := (hb i x).2
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 - w i x) * 1 + w i x * 1 := add_le_add
        (mul_le_mul_of_nonneg_left he1 (by linarith)) (mul_le_mul_of_nonneg_left hf1 hw0)
      _ = 1 := by ring
  · rw [characteristic_gluedRegion]
    exact (((tendsto_const_nhds.sub (ht x)).mul tendsto_const_nhds).add
      ((ht x).mul tendsto_const_nhds)).mul tendsto_const_nhds

lemma normalMeasure_sublevelCutoff_tendsto (μ : FiniteMeasure NormalBundle)
    {q : Cover → ℝ} (hq : Continuous q) (hp : ∀ n x, q (x + latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ ∫ z : NormalBundle, sublevelCutoff q t (ε i) z.1 ∂(μ : Measure NormalBundle))
      atTop (𝓝 ((μ : Measure NormalBundle).real {z | q z.1 < t})) := by
  have hh := tendsto_integral_of_dominated_convergence
    (μ := (μ : Measure NormalBundle)) (bound := fun _ ↦ (1 : ℝ))
    (F := fun i z ↦ sublevelCutoff q t (ε i) z.1)
    (f := {z : NormalBundle | q z.1 < t}.indicator (fun _ ↦ (1 : ℝ)))
    (fun i ↦ (show Continuous (fun z : NormalBundle ↦ sublevelCutoff q t (ε i) z.1) from by
      unfold sublevelCutoff; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun i ↦ Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sublevelCutoff_mem_Icc q t (ε i) z.1).1]
      exact (sublevelCutoff_mem_Icc q t (ε i) z.1).2)
    (Eventually.of_forall fun z ↦ ?_)
  · have hm : MeasurableSet {z : NormalBundle | q z.1 < t} :=
      isOpen_lt (by fun_prop) continuous_const |>.measurableSet
    simpa only [integral_indicator hm, integral_const, smul_eq_mul, mul_one,
      Measure.real_def, Measure.restrict_apply_univ] using hh
  · have he : characteristic (sublevelRegion q t) (quotientMap z.1) =
        {z : NormalBundle | q z.1 < t}.indicator (fun _ ↦ (1 : ℝ)) z := by
      classical
      by_cases hz : q z.1 < t <;> simp [characteristic, mem_sublevelRegion_quotient hp, hz]
    rw [← he]
    exact sublevelCutoff_tendsto hp hε hεlim t z.1

lemma normalMeasure_integral_one (μ : FiniteMeasure NormalBundle) :
    (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = (μ.mass : ℝ) := by
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real_def,
    ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

lemma regionDistance_gluedRegion {E F B : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hF : NullMeasurableSet F torusVolume)
    (hB : NullMeasurableSet B torusVolume) :
    regionDistance E (gluedRegion E F B) = torusVolume.real ((E ∆ F) ∩ B) := by
  have heq (x : Torus) : ‖characteristic E x - characteristic (gluedRegion E F B) x‖ =
      characteristic ((E ∆ F) ∩ B) x := by
    classical
    by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> by_cases hb : x ∈ B <;>
      simp [characteristic, gluedRegion, Set.mem_symmDiff, he, hf, hb]
  unfold regionDistance
  simp_rw [heq]
  exact integral_characteristic ((hE.symmDiff hF).inter hB)

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

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMove_hasFDerivAt (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (normalMove n f)
      (ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight n) x := by
  exact (hasFDerivAt_id x).add (hf.hasFDerivAt.smul_const n)

lemma normalMove_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMove n f) := contDiff_id.add (hf.smul_const n)

lemma normalPullback_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (normalPullback n f F) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hG := hF.comp (normalMove_contDiff n hf)
  exact (contDiff_const.add (hd.clm_apply contDiff_const)).smul hG |>.sub
    ((hd.clm_apply hG).smul contDiff_const)

lemma divergence_comp_normalMove (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) {F : Cover → Cover}
    (hF : DifferentiableAt ℝ F (normalMove n f x)) :
    divergence (fun y ↦ F (normalMove n f y)) x =
      divergence F (normalMove n f x) +
        fderiv ℝ f x (fderiv ℝ F (normalMove n f x) n) := by
  have hd := (hF.hasFDerivAt.comp x (normalMove_hasFDerivAt n hf)).fderiv
  change fderiv ℝ (fun y ↦ F (normalMove n f y)) x = _ at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPullback_divergence (n : Cover) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (normalPullback n f F) x =
      normalJacobian n f x * divergence F (normalMove n f x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := normalMove_hasFDerivAt n hfd
  have hg := (hF.differentiable (by simp)).differentiableAt (x := normalMove n f x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const n x)).const_add 1
  have hb := hdf.hasFDerivAt.clm_apply hu
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)) n (F (normalMove n f x))
  change divergence (fun y ↦ normalJacobian n f y • F (normalMove n f y) -
    fderiv ℝ f y (F (normalMove n f y)) • n) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (normalJacobian n f) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (normalJacobian n f) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ F (normalMove n f y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (F (normalMove n f y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ normalJacobian n f y • F (normalMove n f y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (F (normalMove n f y)) • n) x := hB.smul_const n
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU, divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_normalMove n hfd hg]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, zero_add,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero, smul_eq_mul]
  dsimp only [normalJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphShear_columnChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphShear a n g (normalColumnChart a n (t,y)) = normalColumnChart a n (t+g y,y) := by
  change normalColumnChart a n (t,y) +
    g (normalPlaneCoordinates n (normalColumnChart a n (t,y)-a)) • n = _
  rw [normalColumnChart_projection a hn, normalColumnChart_apply a hn,
    normalColumnChart_apply a hn, add_smul]
  abel

lemma columnShear_measurePreserving {g : Plane → ℝ} (hg : Measurable g) :
    MeasurePreserving (fun p : ℝ × Plane ↦ (p.1+g p.2, p.2)) := by
  have hs : MeasurePreserving (fun p : Plane × ℝ ↦ (p.1, p.2+g p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y ↦ (measurePreserving_add_right volume (g y)).map_eq)
  have hh := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure ℝ))).comp (hs.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))))
  simpa only [Function.comp_def, Prod.swap, Measure.volume_eq_prod] using hh

lemma graphShear_measurePreserving (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Measurable g) : MeasurePreserving (graphShear a n g) := by
  have hi : MeasurePreserving (normalColumnChart a n).symm :=
    MeasurePreserving.symm (normalColumnChart a n) (normalColumnChart_measurePreserving a n)
  have hh := (normalColumnChart_measurePreserving a n).comp
    ((columnShear_measurePreserving hg).comp hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart a n).surjective x
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact graphShear_columnChart a hn g t y

lemma graphHeightExtension_fderiv (a n : Cover) {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (x : Cover) : fderiv ℝ (graphHeightExtension a n g) x =
      (fderiv ℝ g (normalPlaneCoordinates n (x-a))).comp (normalPlaneCoordinates n) := by
  unfold graphHeightExtension
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, graphHeightExtension] using
    ((hg _).hasFDerivAt.comp x hp).fderiv

lemma graphHeightExtension_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    fderiv ℝ (graphHeightExtension a n g) x n = 0 := by
  rw [graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    normalPlaneCoordinates_normal hn, map_zero]

lemma graphShear_jacobian (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    normalJacobian n (graphHeightExtension a n g) x = 1 := by
  rw [normalJacobian, graphHeightExtension_normal a hn hg, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSublevelIndicator_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSublevelIndicator a n g (graphShear a n g x) = halfspaceIndicator n (x-a) := by
  have hheight : ⟪n, graphShear a n g x - a⟫ = ⟪n,x-a⟫ + graphHeightExtension a n g x := by
    simp only [graphShear, normalMove, add_sub_right_comm, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hp : graphHeightExtension a n g (graphShear a n g x) = graphHeightExtension a n g x :=
    congrArg g (graphShear_projection a hn g x)
  simp only [graphSublevelIndicator, Set.indicator, Set.mem_ofPred_eq, hheight, hp,
    add_lt_iff_neg_right, halfspaceIndicator]

lemma normalPullback_graph_compactSupport (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {F : Cover → Cover} (hs : HasCompactSupport F) :
    HasCompactSupport (normalPullback n (graphHeightExtension a n g) F) := by
  have hc := hs.comp_homeomorph (graphShearHomeomorph a hn hg)
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  dsimp only [Function.comp_def, graphShearHomeomorph] at hx
  have hh : F (graphShear a n g x) = 0 := hx
  simp only [Function.mem_support, not_not]
  change normalPullback n (graphHeightExtension a n g) F x = 0
  change F (normalMove n (graphHeightExtension a n g) x) = 0 at hh
  simp only [normalPullback, hh, smul_zero, map_zero, zero_smul, sub_self]

lemma graphAreaVector_pullback (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (F : Cover → Cover) (y : Plane) :
    ⟪n, normalPullback n (graphHeightExtension a n g) F (a+normalPlaneEmbedding n y)⟫ =
      ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hs : graphShear a n g (a+normalPlaneEmbedding n y) = a+normalGraph n g y := by
    simp only [graphShear, normalMove, graphHeightExtension, add_sub_cancel_left,
      normalPlaneCoordinates_embedding, normalGraph]
    abel
  rw [normalPullback, graphShear_jacobian a hn hg, one_smul, ← graphShear, hs,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    add_sub_cancel_left, normalPlaneCoordinates_embedding]
  rw [graphAreaVector, inner_sub_left]
  congr 1
  rw [show normalPlaneEmbedding n (gradient g y) =
    (normalPlaneLinearIsometry n).toContinuousLinearMap (gradient g y) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
  rfl

theorem integral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hmp : MeasurePreserving (graphShearHomeomorph a hn hg.continuous).toMeasurableEquiv :=
    graphShear_measurePreserving a hn hg.continuous.measurable
  rw [← hmp.integral_comp' (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x)]
  have he (x : Cover) : graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
      divergence F (graphShearHomeomorph a hn hg.continuous x) =
      halfspaceIndicator n (x-a) * divergence (normalPullback n (graphHeightExtension a n g) F) x := by
    change graphSublevelIndicator a n g (graphShear a n g x) * divergence F (graphShear a n g x) = _
    rw [graphSublevelIndicator_shear a hn, normalPullback_divergence n
      (graphHeightExtension_contDiff a n hg) hF,
      graphShear_jacobian a hn (hg.differentiable (by simp)), one_mul]
    rfl
  change (∫ x : Cover, graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
    divergence F (graphShearHomeomorph a hn hg.continuous x)) = _
  simp_rw [he]
  rw [integral_halfspace_divergence a hn
    (normalPullback_contDiff n (graphHeightExtension_contDiff a n hg) hF)
    (normalPullback_graph_compactSupport a hn hg.continuous hs)]
  apply integral_congr_ae
  exact Eventually.of_forall (graphAreaVector_pullback a hn (hg.differentiable (by simp)) F)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
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

lemma graph_trace_compactSupport {X : Type*} [Zero X]
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hs : HasCompactSupport F) :
    HasCompactSupport (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  have hc := (hs.comp_homeomorph (graphShearHomeomorph a hn hg)).comp_isClosedEmbedding
    (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
  have he (y : Plane) : graphShearHomeomorph a hn hg (normalColumnChart a n (0,y)) =
      a+normalGraph n g y := by
    change graphShear a n g (normalColumnChart a n (0,y)) = _
    rw [graphShear_columnChart a hn, zero_add, normalColumnChart_apply a hn]
    rfl
  simpa only [Function.comp_def, he] using hc

lemma graphAreaVector_continuous (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphAreaVector n g) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact continuous_const.sub ((normalPlaneLinearIsometry n).continuous.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp hd))

lemma graph_trace_flux_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : Continuous F) (hs : HasCompactSupport F) :
    Integrable (fun y : Plane ↦ ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫) := by
  have hc := graph_trace_compactSupport a hn hg.continuous hs
  have hs' : HasCompactSupport (fun y : Plane ↦ ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫) := by
    apply hc.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro he
    apply hx
    rw [he, inner_zero_right]
  exact ((graphAreaVector_continuous n hg).inner
    (graph_trace_continuous a n hg.continuous hF)).integrable_of_hasCompactSupport hs'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem cutoff_gluing_local_flux_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hb : ∀ x, w x ∈ Icc 0 1)
    {X : Cover → Cover} (hX : AdmissibleField X)
    {A : ℝ} (hlocal : (∫ x in fundamentalCube, characteristic F (quotientMap x) *
      divergence (fun y ↦ w y • X y) x) ≤ A) :
    (∫ x in fundamentalCube,
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x) ≤
      (∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle)) +
      A +
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
  let Y : Cover → Cover := fun x ↦ (1 - w x) • X x
  let Z : Cover → Cover := fun x ↦ w x • X x
  have hY : AdmissibleField Y := admissible_cutoff (contDiff_const.sub hw)
    (fun n x ↦ by rw [hp]) (fun x ↦ by constructor <;> linarith [(hb x).1, (hb x).2]) hX
  have hZ : AdmissibleField Z := admissible_cutoff hw hp hb hX
  let a : Cover → ℝ := fun x ↦ characteristic E (quotientMap x) * divergence Y x
  let b : Cover → ℝ := fun x ↦ characteristic F (quotientMap x) * divergence Z x
  let c : Cover → ℝ := fun x ↦ (characteristic F (quotientMap x) - characteristic E (quotientMap x)) *
    ⟪gradient w x, X x⟫
  have ha : IntegrableOn a fundamentalCube := integrableOn_characteristic_mul hE.nullMeasurableSet
    (integrableOn_divergence hY.1)
  have hb' : IntegrableOn b fundamentalCube := integrableOn_characteristic_mul hF.nullMeasurableSet
    (integrableOn_divergence hZ.1)
  have hi : IntegrableOn (fun x ↦ ⟪gradient w x, X x⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hw).continuous.inner hX.1.continuous)
      (fun n x ↦ by rw [gradient_periodic hp, hX.2.1])
  have hc : IntegrableOn c fundamentalCube := by
    have hh := (integrableOn_characteristic_mul hF.nullMeasurableSet hi).sub
      (integrableOn_characteristic_mul hE.nullMeasurableSet hi)
    simpa only [Pi.sub_def, ← sub_mul, c] using hh
  have hgn : IntegrableOn (fun x ↦ ‖gradient w x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have heq (x : Cover) :
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x = a x + b x - c x := by
    dsimp [a, b, c, Y, Z]
    rw [divergence_smul_function ((contDiff_const.sub hw).differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left]
    ring
  simp_rw [heq]
  have hab : IntegrableOn (fun x ↦ a x + b x) fundamentalCube := by
    simpa only [Pi.add_def] using ha.add hb'
  rw [integral_sub hab hc, integral_add ha hb']
  have hmassE : (∫ x in fundamentalCube, a x) ≤ ∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle) := by
    dsimp only [a]
    simp_rw [characteristic_mul]
    rw [lift_indicator_integral hE.nullMeasurableSet,
      ← normalMeasure_weighted_flux hμ (contDiff_const.sub hw) (fun n x ↦ by rw [hp]) hX]
    have hh : Continuous (fun z : NormalBundle ↦ 1 - w z.1) := by fun_prop
    apply integral_mono ((hh.mul (normalTest X hX.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      (hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro z
    exact mul_le_of_le_one_right (by linarith [(hb z.1).2]) (normalTest_le_one hX z)
  have hmassF : (∫ x in fundamentalCube, b x) ≤ A := hlocal
  have herr : -(∫ x in fundamentalCube, c x) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
    rw [← integral_neg, ← lift_indicator_integral (hE.symmDiff hF).nullMeasurableSet]
    have hci := integrableOn_characteristic_mul (hE.symmDiff hF).nullMeasurableSet hgn
    simp_rw [← characteristic_mul] at ⊢ hci
    apply integral_mono hc.neg hci
    intro x
    calc
      -c x ≤ |c x| := neg_le_abs _
      _ = characteristic (E ∆ F) (quotientMap x) * |⟪gradient w x, X x⟫| := by
        dsimp only [c]
        rw [abs_mul, characteristic_symmDiff_abs]
      _ ≤ characteristic (E ∆ F) (quotientMap x) * ‖gradient w x‖ := by
        apply mul_le_mul_of_nonneg_left _ (characteristic_nonneg _ _)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (hX.2.2 x))
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma measurableSet_torusGraphRegion (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    MeasurableSet (torusGraphRegion a n g) := by
  apply measurableSet_lt
  · exact measurable_const.inner (measurable_representative.sub_const a)
  · exact (hg.comp ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub continuous_const))).measurable.comp measurable_representative

lemma characteristic_torusGraphRegion {x : Cover} (hx : x ∈ fundamentalCube)
    (a n : Cover) (g : Plane → ℝ) :
    characteristic (torusGraphRegion a n g) (quotientMap x) = graphSublevelIndicator a n g x := by
  simp only [characteristic, torusGraphRegion, Set.indicator, Set.mem_ofPred_eq,
    representative_quotientMap_of_mem hx, graphSublevelIndicator]

lemma interior_cutoff_flux_eq (a n : Cover) (g : Plane → ℝ)
    {w : Cover → ℝ} (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (X : Cover → Cover) :
    (∫ x in fundamentalCube, characteristic (torusGraphRegion a n g) (quotientMap x) *
      divergence (fun y ↦ latticePeriodize w y • X y) x) =
      ∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • X y) x := by
  rw [← integral_indicator measurableSet_fundamentalCube]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · rw [indicator_of_mem hx, characteristic_torusGraphRegion hx]
    have he := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).smul
      (EventuallyEq.rfl : X =ᶠ[𝓝 x] X)
    have hd := he.fderiv_eq (𝕜 := ℝ)
    simp only [divergence] at hd ⊢
    rw [hd]
  · rw [indicator_of_notMem hx]
    have hsup : tsupport (fun y ↦ w y • X y) ⊆ tsupport w := tsupport_smul_subset_left w X
    have hdiv : divergence (fun y ↦ w y • X y) x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      exact hx (fun i ↦ ⟨(hs (hsup hh) i).1.le, (hs (hsup hh) i).2⟩)
    rw [hdiv, mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem perimeter_glued_local_flux_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume (E ∆ F) q) d t)
    {L : ℕ → ℝ} {L₀ : ℝ} (hLlim : Tendsto L atTop (𝓝 L₀))
    (hlocal : ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff q t (1 / ((i : ℝ)+1)) y • X y) x) ≤ L i) :
    FinitePerimeter (gluedRegion E F (sublevelRegion q t)) ∧
      (perimeter (gluedRegion E F (sublevelRegion q t))).toReal ≤
        (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
        L₀ + K * M * d := by
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → Cover → ℝ := fun i ↦ sublevelCutoff q t (ε i)
  have hw (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (w i) := sublevelCutoff_contDiff hq t (ε i)
  have hwp (i : ℕ) : ∀ n x, w i (x + latticeVector n) = w i x := sublevelCutoff_periodic hp t (ε i)
  have hwb (i : ℕ) (x : Cover) : w i x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (ε i) x
  have hB := measurableSet_sublevelRegion hq.continuous.measurable t
  have hG := measurableSet_gluedRegion hE hF hB
  let A : ℝ := (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
    L₀ + K * M * d
  have hμlim : Tendsto (fun i ↦ ∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle))
      atTop (𝓝 ((μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t})) := by
    have hh := (tendsto_const_nhds (x := (μ.mass : ℝ)) (f := atTop)).sub
      (normalMeasure_sublevelCutoff_tendsto μ hq.continuous hp he helim t)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    have hi : Integrable (fun z : NormalBundle ↦ w i z.1) (μ : Measure NormalBundle) :=
      (show Continuous (fun z : NormalBundle ↦ w i z.1) from by fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub (integrable_const 1) hi, normalMeasure_integral_one]
  have hdlim := tendsto_backward_quotient_of_hasDerivAt hd he helim
  have hright : Tendsto (fun i ↦
      (∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle)) +
      L i +
      K * M * ((sublevelVolume (E ∆ F) q t - sublevelVolume (E ∆ F) q (t - ε i)) / ε i))
        atTop (𝓝 A) := (hμlim.add hLlim).add (tendsto_const_nhds.mul hdlim)
  have hbound (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' gluedRegion E F (sublevelRegion q t), divergence X x) ≤ A := by
    have hleft := cutoff_gluing_flux_tendsto hE hF hB (fun i ↦ (hw i).continuous) hwb
      (sublevelCutoff_tendsto hp he helim t) hX
    apply le_of_tendsto_of_tendsto' hleft hright
    intro i
    exact (cutoff_gluing_local_flux_le hE hF hμ (hw i) (hwp i) (hwb i) hX (hlocal i X hX)).trans
      (add_le_add_right (sublevelCutoff_gradient_integral_le (hE.symmDiff hF) hq hp hK hgrad (he i)) _)
  have hA : 0 ≤ A := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hb : perimeter (gluedRegion E F (sublevelRegion q t)) ≤ ENNReal.ofReal A := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    exact ENNReal.ofReal_le_ofReal (hbound X hX)
  refine ⟨⟨hG.nullMeasurableSet, hb.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  simpa only [ENNReal.toReal_ofReal hA] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_norm_ge {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖y‖ ≤ ‖normalGraph n g y‖ := by
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (normalGraph n g y) 0
  simpa only [normalPlaneCoordinates_graph hn, map_zero, dist_zero_right,
    NNReal.coe_one, one_mul] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVOrientedGraphCost
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

lemma norm_sub_inner_normalized_le (v w : Cover) (hw : 1 ≤ ‖w‖) :
    ‖v‖ - ⟪v, ‖w‖⁻¹ • w⟫ ≤ ‖v-w‖^2/2 := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw
  have hsq := norm_sub_sq_real v w
  have hquadratic : ‖v‖-⟪v, ‖w‖⁻¹ • w⟫ ≤ ‖v-w‖^2/(2*‖w‖) := by
    rw [le_div_iff₀ (by positivity : 0 < 2*‖w‖), inner_smul_right]
    have he : (‖v‖-‖w‖⁻¹*⟪v,w⟫)*(2*‖w‖) = 2*‖v‖*‖w‖-2*⟪v,w⟫ := by
      field_simp
    rw [he]
    nlinarith [sq_nonneg (‖v‖-‖w‖)]
  apply hquadratic.trans
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)

lemma graphOrientedCost_nonneg (n : Cover) {ν : Cover} (hν : ‖ν‖ ≤ 1)
    (g : Plane → ℝ) (y : Plane) : 0 ≤ graphOrientedCost n ν g y := by
  exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hν))

lemma graphOrientedCost_continuous (n ν : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphOrientedCost n ν g) :=
  (graphAreaVector_continuous n hg).norm.sub ((graphAreaVector_continuous n hg).inner continuous_const)

lemma graphOrientedCost_slope_le {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (p y : Plane) :
    graphOrientedCost n (graphSlopeNormal n p) g y ≤ ‖gradient g y-p‖^2/2 := by
  have hh := norm_sub_inner_normalized_le (graphAreaVector n g y)
    (n-normalPlaneEmbedding n p) (graphSlopeVector_norm_ge hn p)
  have he : graphAreaVector n g y-(n-normalPlaneEmbedding n p) =
      normalPlaneEmbedding n (p-gradient g y) := by
    simp only [graphAreaVector]
    change n-(normalPlaneLinearIsometry n) (gradient g y)-(n-(normalPlaneLinearIsometry n) p) = (normalPlaneLinearIsometry n) (p-gradient g y)
    rw [map_sub]
    abel
  rw [he, normalPlaneEmbedding_norm, norm_sub_rev p] at hh
  exact hh

lemma graphOrientedCost_trace_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (ν : Cover) {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : Continuous w) (hs : HasCompactSupport w) :
    Integrable (fun y ↦ w (a+normalGraph n g y)*graphOrientedCost n ν g y) := by
  exact ((graph_trace_continuous a n hg.continuous hw).mul
    (graphOrientedCost_continuous n ν hg)).integrable_of_hasCompactSupport
      (graph_trace_compactSupport a hn hg.continuous hs).mul_right

lemma integral_graphSublevel_relative_flux_le (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (ν : Cover)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • X y) x) ≤
      (∫ y : Plane, w (a+normalGraph n g y)*graphOrientedCost n ν g y) +
      ∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • ν) x := by
  rw [integral_graphSublevel_divergence a hn hg (F := fun y => w y • X y) (hw.smul hX.1) hs.smul_right,
    integral_graphSublevel_divergence a hn hg (F := fun y => w y • ν) (hw.smul_const ν) hs.smul_right]
  have hi := graphOrientedCost_trace_integrable a hn ν hg hw.continuous hs
  have hj := graph_trace_flux_integrable a hn hg (F := fun y => w y • ν) (hw.continuous.smul (continuous_const (y := ν))) hs.smul_right
  rw [← integral_add hi hj]
  apply integral_mono (graph_trace_flux_integrable a hn hg (F := fun y => w y • X y) (hw.continuous.smul hX.1.continuous) hs.smul_right)
    (hi.add hj)
  intro y
  simp only [Pi.add_apply, inner_smul_right, graphOrientedCost]
  have hh : ⟪graphAreaVector n g y,X (a+normalGraph n g y)⟫ ≤ ‖graphAreaVector n g y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hX.2.2 _))
  nlinarith [mul_le_mul_of_nonneg_left hh (hw0 (a+normalGraph n g y))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma normal_constant_admissible {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    AdmissibleField (fun _ : Cover ↦ ν) :=
  ⟨contDiff_const, fun _ _ ↦ rfl, fun _ ↦ hν⟩

lemma cutoff_constant_flux_sub_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    (∫ x in fundamentalCube, characteristic F (quotientMap x) *
      divergence (fun y ↦ w y • ν) x) ≤
    (∫ x in fundamentalCube, characteristic E (quotientMap x) *
      divergence (fun y ↦ w y • ν) x) +
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
  have hdiv (x : Cover) : divergence (fun y ↦ w y • ν) x = ⟪gradient w x,ν⟫ := by
    rw [divergence_smul_function (hw.differentiable (by simp)).differentiableAt
      (differentiableAt_const ν)]
    simp [divergence]
  simp_rw [hdiv]
  have hi : IntegrableOn (fun x ↦ ⟪gradient w x,ν⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hw).continuous.inner continuous_const)
      (fun n x ↦ by rw [gradient_periodic hp])
  have hgn : IntegrableOn (fun x ↦ ‖gradient w x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have ha := integrableOn_characteristic_mul hF.nullMeasurableSet hi
  have hb := integrableOn_characteristic_mul hE.nullMeasurableSet hi
  rw [← sub_le_iff_le_add', ← integral_sub ha hb,
    ← lift_indicator_integral (hE.symmDiff hF).nullMeasurableSet]
  simp_rw [← characteristic_mul]
  apply integral_mono (ha.sub hb)
    (integrableOn_characteristic_mul (hE.symmDiff hF).nullMeasurableSet hgn)
  intro x
  simp only [Pi.sub_apply]
  rw [← sub_mul]
  calc
    _ ≤ |(characteristic F (quotientMap x)-characteristic E (quotientMap x))*⟪gradient w x,ν⟫| := le_abs_self _
    _ = characteristic (E ∆ F) (quotientMap x)*|⟪gradient w x,ν⟫| := by
      rw [abs_mul, characteristic_symmDiff_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hν))
      (characteristic_nonneg _ _)

lemma cutoff_constant_flux_normal {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x+latticeVector n) = w x)
    {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    (∫ x in fundamentalCube, characteristic E (quotientMap x)*divergence (fun y ↦ w y • ν) x) =
      ∫ z : NormalBundle, w z.1 * ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle) := by
  simp_rw [characteristic_mul]
  rw [lift_indicator_integral hE.nullMeasurableSet,
    ← normalMeasure_weighted_flux hμ hw hp (normal_constant_admissible hν)]
  rfl

lemma normalMeasure_sublevelCutoff_inner_tendsto (μ : FiniteMeasure NormalBundle)
    {q : Cover → ℝ} (hq : Continuous q) (hp : ∀ n x, q (x+latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0))
    (t : ℝ) {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    Tendsto (fun i ↦ ∫ z : NormalBundle, sublevelCutoff q t (ε i) z.1 * ⟪(z.2 : Cover),ν⟫
      ∂(μ : Measure NormalBundle)) atTop
      (𝓝 (∫ z : NormalBundle in {z | q z.1 < t}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle))) := by
  let A : Set NormalBundle := {z | q z.1 < t}
  have hm : MeasurableSet A := isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have hh := tendsto_integral_of_dominated_convergence
    (μ := (μ : Measure NormalBundle)) (bound := fun _ ↦ (1 : ℝ))
    (F := fun i z ↦ sublevelCutoff q t (ε i) z.1 * ⟪(z.2 : Cover),ν⟫)
    (f := A.indicator (fun z ↦ ⟪(z.2 : Cover),ν⟫))
    (fun i ↦ (show Continuous (fun z : NormalBundle ↦ sublevelCutoff q t (ε i) z.1 *
      ⟪(z.2 : Cover),ν⟫) from by unfold sublevelCutoff; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun i ↦ Eventually.of_forall fun z ↦ ?_)
    (Eventually.of_forall fun z ↦ ?_)
  · simpa only [integral_indicator hm] using hh
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sublevelCutoff_mem_Icc q t (ε i) z.1).1]
    have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
    have hh : ‖⟪(z.2 : Cover),ν⟫‖ ≤ 1 := by
      exact (norm_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν)
    exact (mul_le_mul_of_nonneg_left hh (sublevelCutoff_mem_Icc q t (ε i) z.1).1).trans
      (by simpa only [mul_one] using (sublevelCutoff_mem_Icc q t (ε i) z.1).2)
  · have he : A.indicator (fun z ↦ ⟪(z.2 : Cover),ν⟫) z =
        characteristic (sublevelRegion q t) (quotientMap z.1)*⟪(z.2 : Cover),ν⟫ := by
      classical
      by_cases hz : q z.1 < t <;> simp [A, characteristic, mem_sublevelRegion_quotient hp, hz]
    rw [he]
    exact (sublevelCutoff_tendsto hp hε hεlim t z.1).mul tendsto_const_nhds

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphBallOrientedCost_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ν : Cover} (hν : ‖ν‖ ≤ 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y : Plane, radialDensityWeight a r (ε i) (a+normalGraph n g y) *
      graphOrientedCost n ν g y) atTop (𝓝 (graphBallOrientedCost a n ν g r)) := by
  have hm : MeasurableSet {y : Plane | a+normalGraph n g y ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (graph_trace_continuous a n hg.continuous
      continuous_id).measurable
  have heps : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hεlim, Eventually.of_forall hε⟩
  have hh := tendsto_integral_of_dominated_convergence
    (bound := fun y : Plane ↦ radialHeightCutoff a r (a+normalGraph n g y) * graphOrientedCost n ν g y)
    (F := fun i y ↦ radialDensityWeight a r (ε i) (a+normalGraph n g y) * graphOrientedCost n ν g y)
    (f := fun y ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) (a+normalGraph n g y) *
      graphOrientedCost n ν g y)
    (fun i ↦ (graphOrientedCost_trace_integrable a hn ν hg
      (radialDensityWeight_contDiff a r (ε i)).continuous
      (radialDensityWeight_hasCompactSupport hr.le (hε i))).aestronglyMeasurable)
    (graphOrientedCost_trace_integrable a hn ν hg (radialDensityWeight_contDiff a (2*r) (3*r^2)).continuous
      (radialDensityWeight_hasCompactSupport (by positivity : 0 ≤ 2*r) (by positivity : 0 < 3*r^2)))
    (fun i ↦ Eventually.of_forall fun y ↦ ?_)
    (Eventually.of_forall fun y ↦ ((radialDensityWeight_tendsto a (a+normalGraph n g y) hr).comp heps).mul
      tendsto_const_nhds)
  · convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [graphBallOrientedCost, ← integral_indicator hm]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : a+normalGraph n g y ∈ Metric.ball a r <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, hy, ite_true, ite_false, one_mul, zero_mul]
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (radialDensityWeight_nonneg _ _ _ _)
      (graphOrientedCost_nonneg n hν g y))]
    apply mul_le_mul_of_nonneg_right _ (graphOrientedCost_nonneg n hν g y)
    by_cases hy : a+normalGraph n g y ∈ Metric.closedBall a r
    · rw [radialHeightCutoff_one hr hy]
      exact radialDensityWeight_le_one _ _ _ _
    · have hd : r ≤ ‖(a+normalGraph n g y)-a‖ := le_of_lt (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hy)
      rw [radialDensityWeight_zero hr.le (hε i) hd]
      exact Real.smoothTransition.nonneg _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeGradient_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient g) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp))

lemma smooth_graph_relative_energy_integrable {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : Plane) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖gradient g y-p‖^2) (Metric.ball (0 : Plane) r) := by
  apply (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) r)
    ((((planeGradient_contDiff hg).continuous.sub continuous_const).norm).pow 2).continuousOn).mono_set
    Metric.ball_subset_closedBall

lemma graphBallOrientedCost_le_disk (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : Plane) (r : ℝ) :
    graphBallOrientedCost a n (graphSlopeNormal n p) g r ≤
      (∫ y in Metric.ball (0 : Plane) r, ‖gradient g y-p‖^2)/2 := by
  let S : Set Plane := {y | a+normalGraph n g y ∈ Metric.ball a r}
  have hsub : S ⊆ Metric.ball (0 : Plane) r := by
    intro y hy
    have hh : ‖normalGraph n g y‖ < r := by
      simpa only [S, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hy
    simpa only [Metric.mem_ball, dist_zero_right] using (normalGraph_norm_ge hn g y).trans_lt hh
  have hi := smooth_graph_relative_energy_integrable hg p r
  have hcost : IntegrableOn (graphOrientedCost n (graphSlopeNormal n p) g) (Metric.ball (0 : Plane) r) :=
    ((graphOrientedCost_continuous n _ hg).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) r)).mono_set Metric.ball_subset_closedBall
  calc
    _ ≤ ∫ y in S, ‖gradient g y-p‖^2/2 :=
      integral_mono (hcost.mono_set hsub) (IntegrableOn.mono_set (hi.div_const 2) hsub)
        (graphOrientedCost_slope_le hn g p)
    _ ≤ ∫ y in Metric.ball (0 : Plane) r, ‖gradient g y-p‖^2/2 :=
      setIntegral_mono_set (hi.div_const 2) (Eventually.of_forall fun y ↦ by positivity)
        hsub.eventuallyLE
    _ = _ := by rw [integral_div]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma sublevelVolume_relative_difference {E F G : Set Torus} {q : Cover → ℝ}
    (hq : Measurable q) {s t : ℝ} (hst : s ≤ t)
    (hchange : F ∆ G ⊆ sublevelRegion q s) :
    sublevelVolume (E ∆ G) q t-sublevelVolume (E ∆ F) q t =
      sublevelVolume (E ∆ G) q s-sublevelVolume (E ∆ F) q s := by
  have hsub : sublevelRegion q s ⊆ sublevelRegion q t := fun x hx ↦ lt_of_lt_of_le hx hst
  have hg := measureReal_inter_add_sdiff (μ := torusVolume)
    (s := (E ∆ G) ∩ sublevelRegion q t) (measurableSet_sublevelRegion hq s)
  have hf := measureReal_inter_add_sdiff (μ := torusVolume)
    (s := (E ∆ F) ∩ sublevelRegion q t) (measurableSet_sublevelRegion hq s)
  have hi (A : Set Torus) : (A ∩ sublevelRegion q t) ∩ sublevelRegion q s = A ∩ sublevelRegion q s := by
    ext x
    simp only [mem_inter_iff]
    exact ⟨fun hx ↦ ⟨hx.1.1,hx.2⟩, fun hx ↦ ⟨⟨hx.1,hsub hx.2⟩,hx.2⟩⟩
  have he : ((E ∆ G) ∩ sublevelRegion q t) \ sublevelRegion q s =
      ((E ∆ F) ∩ sublevelRegion q t) \ sublevelRegion q s := by
    ext x
    have hx : x ∉ sublevelRegion q s → (x ∈ F ↔ x ∈ G) := by
      intro hxs
      by_contra hh
      have hm : x ∈ F ∆ G := by
        simp only [Set.mem_symmDiff]
        tauto
      exact hxs (hchange hm)
    simp only [Set.mem_sdiff, mem_inter_iff, Set.mem_symmDiff]
    constructor <;> intro hh
    · have he := hx hh.2
      tauto
    · have he := hx hh.2
      tauto
  rw [hi] at hg hf
  rw [he] at hg
  dsimp only [sublevelVolume]
  linarith

lemma hasDerivAt_sublevelVolume_of_interior_change {E F G : Set Torus} {q : Cover → ℝ}
    (hq : Measurable q) {s t d : ℝ} (hst : s < t)
    (hchange : F ∆ G ⊆ sublevelRegion q s)
    (hd : HasDerivAt (sublevelVolume (E ∆ F) q) d t) :
    HasDerivAt (sublevelVolume (E ∆ G) q) d t := by
  let c := sublevelVolume (E ∆ G) q s-sublevelVolume (E ∆ F) q s
  have he : sublevelVolume (E ∆ G) q =ᶠ[𝓝 t] fun u ↦ sublevelVolume (E ∆ F) q u+c := by
    filter_upwards [eventually_gt_nhds hst] with u hu
    have hh := sublevelVolume_relative_difference (E := E) hq hu.le hchange
    dsimp only [c]
    linarith
  exact (hd.add_const c).congr_of_eventuallyEq he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma graphBlend_contDiff {χ g u : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiff ℝ (⊤ : ℕ∞) (graphBlend χ g u) :=
  hg.add (hχ.mul (hu.sub hg))

lemma graphBlend_eq_of_zero {χ g u : Plane → ℝ} {y : Plane} (h : χ y = 0) :
    graphBlend χ g u y = g y := by simp [graphBlend,h]

lemma graphBlend_abs_le {χ g u : Plane → ℝ} {y : Plane} {H : ℝ}
    (hχ : χ y ∈ Icc 0 1) (hg : |g y| ≤ H) (hu : |u y| ≤ H) :
    |graphBlend χ g u y| ≤ H := by
  have he : graphBlend χ g u y = (1-χ y)*g y+χ y*u y := by dsimp [graphBlend]; ring
  rw [he]
  calc
    _ ≤ |(1-χ y)*g y|+|χ y*u y| := abs_add_le _ _
    _ = (1-χ y)*|g y|+χ y*|u y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hχ.2),abs_of_nonneg hχ.1]
    _ ≤ (1-χ y)*H+χ y*H := add_le_add
      (mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hχ.2)) (mul_le_mul_of_nonneg_left hu hχ.1)
    _ = H := by ring

lemma graphBlend_fderiv {χ g u : Plane → ℝ} {y : Plane}
    (hχ : DifferentiableAt ℝ χ y) (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (graphBlend χ g u) y =
      (1-χ y) • fderiv ℝ g y + χ y • fderiv ℝ u y +
        (u y-g y) • fderiv ℝ χ y := by
  unfold graphBlend
  have hh := (hg.hasFDerivAt.add (hχ.hasFDerivAt.mul (hu.hasFDerivAt.sub hg.hasFDerivAt))).fderiv
  change fderiv ℝ (fun y ↦ g y + χ y*(u y-g y)) y = _ at hh
  dsimp only [Pi.sub_apply] at hh
  rw [hh]
  module

lemma norm_add_three_sq_le {X : Type*} [NormedAddCommGroup X] (a b c : X) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

lemma graphBlend_relative_energy_pointwise {χ g u : Plane → ℝ} {y : Plane}
    (hχ : DifferentiableAt ℝ χ y) (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableAt ℝ u y) (hb : χ y ∈ Icc 0 1)
    (p : Plane →L[ℝ] ℝ) :
    ‖fderiv ℝ (graphBlend χ g u) y-p‖^2 ≤
      3*((1-χ y)^2*‖fderiv ℝ g y-p‖^2+‖fderiv ℝ u y-p‖^2+
        (u y-g y)^2*‖fderiv ℝ χ y‖^2) := by
  have he : fderiv ℝ (graphBlend χ g u) y-p =
      (1-χ y) • (fderiv ℝ g y-p)+χ y • (fderiv ℝ u y-p)+
        (u y-g y) • fderiv ℝ χ y := by
    rw [graphBlend_fderiv hχ hg hu]
    module
  rw [he]
  have h := norm_add_three_sq_le ((1-χ y) • (fderiv ℝ g y-p))
    (χ y • (fderiv ℝ u y-p)) ((u y-g y) • fderiv ℝ χ y)
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
  have hc : (χ y)^2*‖fderiv ℝ u y-p‖^2 ≤ ‖fderiv ℝ u y-p‖^2 := by
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [hb.1,hb.2])
  linarith

lemma graphBlend_relative_energy_cutoff {χ g u : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hb : ∀ y, χ y ∈ Icc 0 1)
    {D s b : ℝ} (hD : 0 ≤ D) (hd : ∀ y, ‖fderiv ℝ χ y‖ ≤ D)
    (hone : ∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1)
    (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ g u) y-p‖^2) ≤
      3*((∫ y in Metric.ball (0 : Plane) b \ Metric.ball 0 s, ‖fderiv ℝ g y-p‖^2)+
        (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ u y-p‖^2)+
        D^2*(∫ y in Metric.ball (0 : Plane) b, (u y-g y)^2)) := by
  let B := Metric.ball (0 : Plane) b
  let S := Metric.ball (0 : Plane) s
  have hi (f : Plane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      IntegrableOn (fun y ↦ ‖fderiv ℝ f y-p‖^2) B :=
    ((((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) b)).mono_set Metric.ball_subset_closedBall
  have hid : IntegrableOn (fun y ↦ (u y-g y)^2) B :=
    (((hu.continuous.sub hg.continuous).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) b)).mono_set Metric.ball_subset_closedBall
  have hind : IntegrableOn (Sᶜ.indicator (fun y ↦ ‖fderiv ℝ g y-p‖^2)) B :=
    (hi g hg).indicator measurableSet_ball.compl
  have hh : (∫ y in B, ‖fderiv ℝ (graphBlend χ g u) y-p‖^2) ≤
      ∫ y in B, 3*(Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+
        ‖fderiv ℝ u y-p‖^2+D^2*(u y-g y)^2) := by
    apply integral_mono (hi _ (graphBlend_contDiff hχ hg hu))
      (((Integrable.add hind (hi u hu)).add (hid.const_mul _)).const_mul _)
    intro y
    have hp := graphBlend_relative_energy_pointwise
      (hχ.differentiable (by simp)).differentiableAt
      (hg.differentiable (by simp)).differentiableAt
      (hu.differentiable (by simp)).differentiableAt (hb y) p
    have ha : (1-χ y)^2*‖fderiv ℝ g y-p‖^2 ≤ Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y := by
      by_cases hy : y ∈ S
      · simp [indicator_of_notMem (show y ∉ Sᶜ from fun h ↦ h hy),hone y hy]
      · rw [indicator_of_mem hy]
        apply mul_le_of_le_one_left (sq_nonneg _)
        have hyb := hb y
        nlinarith [hyb.1,hyb.2]
    have hc : (u y-g y)^2*‖fderiv ℝ χ y‖^2 ≤ D^2*(u y-g y)^2 := by
      have hsq := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hd y)
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (u y-g y))]
    change ‖fderiv ℝ (graphBlend χ g u) y-p‖^2 ≤ 3*(Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+‖fderiv ℝ u y-p‖^2+D^2*(u y-g y)^2)
    linarith
  calc
    _ ≤ _ := hh
    _ = _ := by
      rw [integral_const_mul,integral_add (f := fun y ↦ Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+‖fderiv ℝ u y-p‖^2) (g := fun y ↦ D^2*(u y-g y)^2) (Integrable.add hind (hi u hu)) (hid.const_mul _),
        integral_add (μ := volume.restrict B) hind (hi u hu),integral_const_mul]
      rw [integral_indicator measurableSet_ball.compl,Measure.restrict_restrict measurableSet_ball.compl]
      rw [show Sᶜ ∩ B = Metric.ball (0 : Plane) b \ Metric.ball 0 s by
        ext y; simp [B,S,and_comm]]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVAnnulusSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma plane_relative_gradient_norm (f : Plane → ℝ) (y : Plane) (p : Plane →L[ℝ] ℝ) :
    ‖gradient f y-(InnerProductSpace.toDual ℝ Plane).symm p‖ = ‖fderiv ℝ f y-p‖ := by
  rw [gradient,← map_sub,(InnerProductSpace.toDual ℝ Plane).symm.norm_map]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CubicTorus

lemma planeAnnulus_pairwise {ρ δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (fun i j ↦ Disjoint (planeAnnulus ρ δ i) (planeAnnulus ρ δ j)) := by
  intro i j hij
  wlog hle : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hle) hij.symm)).symm
  apply disjoint_left.mpr
  intro x hxi hxj
  apply hxj.2
  apply Metric.ball_subset_ball (show ρ+(i+1)*δ ≤ ρ+j*δ from ?_) hxi.1
  have hc : (i : ℝ)+1 ≤ j := by exact_mod_cast hle
  nlinarith

lemma planeAnnulus_subset {ρ δ : ℝ} (hδ : 0 ≤ δ) {N i : ℕ} (hi : i < N) :
    planeAnnulus ρ δ i ⊆ Metric.ball (0 : Plane) (ρ+N*δ) := by
  intro x hx
  apply Metric.ball_subset_ball (show ρ+(i+1)*δ ≤ ρ+N*δ from ?_) hx.1
  have hc : (i : ℝ)+1 ≤ N := by exact_mod_cast hi
  nlinarith

lemma planeAnnulus_integral_pigeonhole {ρ δ : ℝ} (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {f : Plane → ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Plane) (ρ+N*δ)))
    (hpos : ∀ x, 0 ≤ f x) :
    ∃ i : Fin N, (∫ x in planeAnnulus ρ δ i, f x) ≤
      (∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x)/(N : ℝ) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hsum : (∑ i : Fin N, ∫ x in planeAnnulus ρ δ i, f x) ≤
      ∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x := by
    rw [← integral_iUnion_fintype (s := fun i : Fin N ↦ planeAnnulus ρ δ i)
      (fun _ ↦ measurableSet_ball.diff measurableSet_ball)
      (fun i j hij ↦ planeAnnulus_pairwise hδ (Fin.val_ne_of_ne hij))
      (fun i ↦ hf.mono_set (planeAnnulus_subset hδ i.isLt))]
    exact setIntegral_mono_set hf (Eventually.of_forall hpos)
      (iUnion_subset fun i ↦ planeAnnulus_subset hδ i.isLt).eventuallyLE
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (∑ _i : Fin N, (∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x)/(N : ℝ)) =
      ∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    Finset.univ_nonempty (hsum.trans_eq hc.symm)
  exact ⟨i,hi⟩

lemma finite_subsequence_constant {ι : Type*} [Finite ι] (f : ℕ → ι) :
    ∃ i : ι, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, f (ψ k) = i := by
  obtain ⟨i,hi⟩ := Finite.exists_infinite_fiber f
  have hh : ∃ᶠ k in atTop, f k = i := by
    apply Nat.frequently_atTop_iff_infinite.mpr
    exact Set.infinite_coe_iff.mp hi
  obtain ⟨ψ,hψ,hf⟩ := extraction_of_frequently_atTop hh
  exact ⟨i,ψ,hψ,hf⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_fderiv_relative_integrable {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : Plane →L[ℝ] ℝ) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ g y-p‖^2) (Metric.ball (0 : Plane) r) :=
  ((((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Plane) r)).mono_set Metric.ball_subset_closedBall

lemma exists_plane_interpolation_bump {s q : ℝ} (hs : 0 < s) (hsq : s < q) :
    ∃ (χ : Plane → ℝ) (D : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ 0 ≤ D ∧
      (∀ y, ‖fderiv ℝ χ y‖ ≤ D) ∧ (∀ y, χ y ∈ Icc 0 1) ∧
      (∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1) ∧
      (∀ y, q ≤ ‖y‖ → χ y = 0) := by
  let χ : ContDiffBump (0 : Plane) := ⟨s,q,hs,hsq⟩
  obtain ⟨D,hD⟩ := (χ.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((χ.contDiff : ContDiff ℝ (⊤ : ℕ∞) χ).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  refine ⟨χ,max D 0,χ.contDiff,le_max_right _ _,fun y ↦ (hD y).trans (le_max_left _ _),
    fun y ↦ ⟨χ.nonneg,χ.le_one⟩,fun y hy ↦ χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),?_⟩
  intro y hy
  exact χ.zero_of_le_dist (by simpa only [dist_zero_right] using hy)

theorem strong_L2_annulus_replacement {θ : ℝ} (hθ : 0 < θ)
    (f : ℕ → Plane → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p : Plane →L[ℝ] ℝ)
    {A H : ℝ} (_hA : 0 ≤ A)
    (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
    (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
    (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s q a b D : ℝ) (χ : Plane → ℝ) (ψ : ℕ → ℕ),
      θ ≤ s ∧ s < q ∧ q < a ∧ a < b ∧ b ≤ 2*θ ∧ StrictMono ψ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ 0 ≤ D ∧ (∀ y, ‖fderiv ℝ χ y‖ ≤ D) ∧
      (∀ y, χ y ∈ Icc 0 1) ∧ (∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1) ∧
      (∀ y, q ≤ ‖y‖ → χ y = 0) ∧
      ∀ᶠ i in atTop, (∫ y in Metric.ball (0 : Plane) b,
        ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2) ≤ 3*H+ε := by
  obtain ⟨N,hNlarge⟩ := exists_nat_gt (max 0 (6*A/ε))
  have hNr : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hNlarge
  have hN : 0 < N := by exact_mod_cast hNr
  have hsmall : A/(N : ℝ) < ε/6 := by
    have hlarge : 6*A/ε < N := (le_max_right _ _).trans_lt hNlarge
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hNr]
    nlinarith
  let δ := θ/(N : ℝ)
  have hδ : 0 < δ := div_pos hθ hNr
  have heq : θ+(N : ℝ)*δ = 2*θ := by dsimp [δ]; field_simp; ring
  have hex (i : ℕ) : ∃ j : Fin N, (∫ y in planeAnnulus θ δ j, ‖fderiv ℝ (f i) y-p‖^2) ≤ A/N := by
    obtain ⟨j,hj⟩ := planeAnnulus_integral_pigeonhole hδ.le hN
      (f := fun y ↦ ‖fderiv ℝ (f i) y-p‖^2)
      (heq ▸ plane_fderiv_relative_integrable (hf i) p (2*θ)) (fun y ↦ sq_nonneg _)
    refine ⟨j,hj.trans ?_⟩
    rw [heq]
    exact div_le_div_of_nonneg_right (henergy i) hNr.le
  choose j hj using hex
  obtain ⟨k,ψ,hψ,hconst⟩ := finite_subsequence_constant j
  let s := θ+(k : ℝ)*δ
  let b := θ+((k : ℝ)+1)*δ
  let q := (2*s+b)/3
  let a := (s+2*b)/3
  have hs : θ ≤ s := by
    have hk : 0 ≤ (k : ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    dsimp [s]
    linarith
  have hsb : s < b := by dsimp [s,b]; nlinarith
  have hb : b ≤ 2*θ := by
    have hk : (k : ℝ)+1 ≤ N := by exact_mod_cast k.isLt
    rw [← heq]
    dsimp [b]
    nlinarith
  have hsq : s < q := by dsimp [q]; linarith
  have hqa : q < a := by dsimp [q,a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  obtain ⟨χ,D,hχ,hD,hd,hχb,hone,hzero⟩ := exists_plane_interpolation_bump (hθ.trans_le hs) hsq
  refine ⟨s,q,a,b,D,χ,ψ,hs,hsq,hqa,hab,hb,hψ,hχ,hD,hd,hχb,hone,hzero,?_⟩
  have hc : Tendsto (fun i ↦ D^2*(∫ y in Metric.ball (0 : Plane) (2*θ), (f (ψ i) y-u y)^2))
      atTop (𝓝 0) := by simpa using (hconv.comp hψ.tendsto_atTop).const_mul (D^2)
  filter_upwards [hc.eventually (gt_mem_nhds (show 0 < ε/6 by positivity))] with i hi
  have hdiff : D^2*(∫ y in Metric.ball (0 : Plane) b, (u y-f (ψ i) y)^2) ≤
      D^2*(∫ y in Metric.ball (0 : Plane) (2*θ), (f (ψ i) y-u y)^2) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    have hsq (y : Plane) : (u y-f (ψ i) y)^2 = (f (ψ i) y-u y)^2 := by ring
    simp_rw [hsq]
    exact setIntegral_mono_set
      ((((hf (ψ i)).continuous.sub hu.continuous).pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Plane) (2*θ)) |>.mono_set Metric.ball_subset_closedBall)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hb).eventuallyLE
  have hharm : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ u y-p‖^2) ≤ H :=
    (setIntegral_mono_set (plane_fderiv_relative_integrable hu p (2*θ))
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hb).eventuallyLE).trans hH
  have hring : (∫ y in Metric.ball (0 : Plane) b \ Metric.ball 0 s, ‖fderiv ℝ (f (ψ i)) y-p‖^2) ≤ A/N := by
    have hh := hj (ψ i)
    rw [hconst i] at hh
    exact hh
  have hh := graphBlend_relative_energy_cutoff hχ (hf (ψ i)) hu hχb hD hd hone p (b := b)
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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
open Laplacian
namespace CubicTorus

lemma fderiv_comp_smul_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} {r : ℝ} (hf : DifferentiableAt ℝ f (r • x)) :
    fderiv ℝ (fun y ↦ f (r • y)) x = r • fderiv ℝ f (r • x) := by
  have hh := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  have he : (fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ X) =
      r • fderiv ℝ f (r • x) := by ext y; simp
  simpa only [Function.comp_def, id_eq, he] using hh.fderiv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphRescale_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (r e m : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (graphRescale r e m f) := by
  exact contDiff_const.mul (contDiff_const.add (contDiff_const.mul (hf.comp (by fun_prop))))

lemma graphRescale_fderiv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : r ≠ 0) (e m : ℝ) (y : Plane) :
    fderiv ℝ (graphRescale r e m f) y = e • fderiv ℝ f (r⁻¹ • y) := by
  have hd : DifferentiableAt ℝ (fun y : Plane ↦ f (r⁻¹ • y)) y :=
    (hf.comp (by fun_prop)).differentiable (by simp) |>.differentiableAt
  unfold graphRescale
  rw [fderiv_const_mul ((hd.const_mul e).const_add m),
    fderiv_const_add m, fderiv_const_mul hd,
    fderiv_comp_smul_eq ((hf.differentiable (by simp)) _), smul_smul,smul_smul]
  congr 1
  field_simp

lemma plane_integral_rescale_ball (f : Plane → ℝ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), f (r⁻¹ • y)) =
      r^2 * ∫ y in Metric.ball (0 : Plane) b, f y := by
  have he (y : Plane) : r⁻¹ • y ∈ Metric.ball (0 : Plane) b ↔
      y ∈ Metric.ball (0 : Plane) (r*b) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    rw [← div_eq_inv_mul,div_lt_iff₀ hr]
    rw [mul_comm b r]
  have hh := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Plane)
    ((Metric.ball (0 : Plane) b).indicator f) hr.le
  have hh' : (fun y : Plane ↦ (Metric.ball (0 : Plane) b).indicator f (r⁻¹ • y)) =
      (Metric.ball (0 : Plane) (r*b)).indicator (fun y ↦ f (r⁻¹ • y)) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Plane) (r*b)
    · rw [indicator_of_mem hy,indicator_of_mem ((he y).mpr hy)]
    · rw [indicator_of_notMem hy,indicator_of_notMem (fun h ↦ hy ((he y).mp h))]
  rw [hh',integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at hh
  simpa only [show Module.finrank ℝ Plane = 2 from finrank_euclideanSpace_fin,smul_eq_mul] using hh

lemma graphRescale_relative_energy {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : 0 < r) (e m b : ℝ) (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ (graphRescale r e m f) y-e • p‖^2) =
      r^2*e^2*(∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ f y-p‖^2) := by
  simp_rw [graphRescale_fderiv hf hr.ne',← smul_sub,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs]
  rw [integral_const_mul,plane_integral_rescale_ball (fun y ↦ ‖fderiv ℝ f y-p‖^2) hr]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
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
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet ((cubeBall c) r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 3 / 8) :
    Metric.ball (c : Cover) r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - (c : Cover)‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans_lt hx'
  change ‖x i - (c : Cover) i‖ < r at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 3 / 8) :
    fundamentalCube ∩ quotientMap ⁻¹' (cubeBall c) r = Metric.ball (c : Cover) r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball (c : Cover) r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball (c : Cover) r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 3 / 8) :
    torusVolume ((cubeBall c) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) (radialCore c) := by
  exact (radialBump c).contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport (radialCore c) :=
  (radialBump c).hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport (radialCore c) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport ((radialBump c) : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [(radialBump c).tsupport_eq] at hs
  have hnorm : ‖x - (c : Cover)‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans hnorm
  change ‖x i - (c : Cover) i‖ ≤ 1 / 3 at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) (radialSquared c) :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    (radialSquared c) (x + latticeVector n) = (radialSquared c) x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    (radialSquared c) x = 1 - (radialBump c) x * (1 - ‖x - (c : Cover)‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - (c : Cover)‖ < 1 / 4) :
    (radialSquared c) =ᶠ[𝓝 x] (fun y ↦ ‖y - (c : Cover)‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 3 / 8)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := (radialBump c).eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball (c : Cover) (radialBump c).rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    (radialSquared c) x < t ↔ ‖x - (c : Cover)‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - (c : Cover))
  have hb0 : 0 ≤ (radialBump c) x := (radialBump c).nonneg
  have hb1 : (radialBump c) x ≤ 1 := (radialBump c).le_one
  have he (h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16) : (radialBump c) x = 1 := by
    apply (radialBump c).one_of_mem_closedBall
    change dist x (c : Cover) ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - (c : Cover)‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion (radialSquared c) (r ^ 2) = (cubeBall c) r := by
  ext z
  change (radialSquared c) (representative z) < r ^ 2 ↔
    dist (representative z) (c : Cover) < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma norm_gradient_radialSquared_of_mem_cube {x : Cover} (hx : x ∈ fundamentalCube)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (hxt : (radialSquared c) x < r ^ 2) :
    ‖gradient (radialSquared c) x‖ ≤ 2 * r := by
  have hnormsq := (radialSquared_sublevel_iff hx (by nlinarith)).1 hxt
  have hnorm : ‖x - (c : Cover)‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr).mp hnormsq
  rw [norm_gradient_eq_norm_fderiv,
    (radialSquared_eventuallyEq_norm_sq (hnorm.trans_le hsmall)).fderiv_eq]
  have he : (fun y : Cover ↦ ‖y - (c : Cover)‖ ^ 2) =
      (fun y : Cover ↦ ‖y + -(c : Cover)‖ ^ 2) := by simp only [sub_eq_add_neg]
  rw [he]
  have hf : fderiv ℝ (fun y : Cover ↦ ‖y + -(c : Cover)‖ ^ 2) x =
      fderiv ℝ (fun y : Cover ↦ ‖y‖ ^ 2) (x + -(c : Cover)) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Cover ↦ ‖y‖ ^ 2) (x := x) (-(c : Cover)) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hf, fderiv_norm_sq_apply, two_smul]
  calc
    _ ≤ ‖innerSL ℝ (x + -(c : Cover))‖ + ‖innerSL ℝ (x + -(c : Cover))‖ := norm_add_le _ _
    _ = 2 * ‖x - (c : Cover)‖ := by rw [innerSL_apply_norm]; simp only [sub_eq_add_neg]; ring
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm.le (by norm_num)

lemma norm_gradient_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (x : Cover)
    (hxt : (radialSquared c) x < r ^ 2) : ‖gradient (radialSquared c) x‖ ≤ 2 * r := by
  have he := periodic_representative (radialSquared_periodic (c := c)) x
  have hg := periodic_representative (f := gradient (radialSquared c))
    (fun n y ↦ gradient_periodic radialSquared_periodic n y) x
  rw [← hg]
  exact norm_gradient_radialSquared_of_mem_cube (representative_mem_fundamentalCube _) hr hsmall (by rwa [he])

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVMovingOrientedReplacement
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma radialDensityWeight_cell_support {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 3/8) (hε : 0 < ε) :
    tsupport (radialDensityWeight (c : Cover) r ε) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := radialDensityWeight_tsupport hr hε hx
  have hd : ‖x-(c : Cover)‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
  have hi := (PiLp.norm_apply_le (x-(c : Cover)) i).trans hd
  change ‖x i - (c : Cover) i‖ ≤ r at hi
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hi
  constructor <;> linarith

lemma radialDensityWeight_periodize {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/4) (hε : 0 < ε) :
    latticePeriodize (radialDensityWeight (c : Cover) r ε) = sublevelCutoff (radialSquared c) (r^2) ε := by
  funext x
  rw [← periodic_representative (latticePeriodize_periodic _) x,
    ← periodic_representative (sublevelCutoff_periodic radialSquared_periodic (r^2) ε) x]
  let z := representative (quotientMap x)
  have hz : z ∈ fundamentalCube := representative_mem_fundamentalCube _
  rw [(latticePeriodize_eventuallyEq (radialDensityWeight_hasCompactSupport (a := (c : Cover)) hr hε)
    (radialDensityWeight_cell_support hr (by linarith) hε)
    (fun i ↦ ⟨(hz i).1, (hz i).2.le⟩)).eq_of_nhds]
  change radialDensityWeight (c : Cover) r ε z = sublevelCutoff (radialSquared c) (r^2) ε z
  by_cases hz' : ‖z-(c : Cover)‖ < r
  · have he := (radialSquared_eventuallyEq_norm_sq (hz'.trans hs)).eq_of_nhds
    simp only [radialDensityWeight, sublevelCutoff, he]
  · have hh : ¬ (radialSquared c) z < r^2 := by
      rw [radialSquared_sublevel_iff hz (by nlinarith)]
      have hb : r ≤ ‖z-(c : Cover)‖ := le_of_not_gt hz'
      nlinarith [norm_nonneg (z-(c : Cover))]
    rw [radialDensityWeight_zero hr hε (le_of_not_gt hz')]
    exact (Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt hh)) hε.le)).symm

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma bundleOrientedExcess_eq (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) :
    (bundleOrientedExcess c) μ ν r = (μ : Measure NormalBundle).real {z | (radialSquared c) z.1 < r^2} -
      ∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle) := by
  rw [bundleOrientedExcess, integral_sub (integrable_const 1)
    ((show Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply_univ]

theorem isMinimizerAt_oriented_graph_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (ν : Cover), ‖ν‖ ≤ 1 → ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ r K d : ℝ, 0 < r → r < 1/4 → (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      HasDerivAt (sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c)) d (r^2) →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (r^2) < η →
      (bundleOrientedExcess c) μ ν r ≤ graphBallOrientedCost (c : Cover) n ν g r +
        2*K*(2*r)*d + C*sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (r^2) := by
  obtain ⟨η,C,hη,hC,hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η,C,hη,hC,?_⟩
  intro c n hn ν hν g hg r K d hr hs hK hd ht
  let F := torusGraphRegion (c : Cover) n g
  have hF : MeasurableSet F := measurableSet_torusGraphRegion _ _ hg.continuous
  let ε : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let m := sublevelVolume (E ∆ F) (radialSquared c)
  let A : ℕ → ℝ := fun i ↦ ∫ y : Plane, radialDensityWeight (c : Cover) r (ε i)
    ((c : Cover)+normalGraph n g y)*graphOrientedCost n ν g y
  let N : ℕ → ℝ := fun i ↦ ∫ z : NormalBundle, sublevelCutoff (radialSquared c) (r^2) (ε i) z.1 *
    ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)
  let D : ℕ → ℝ := fun i ↦ K*(2*r)*((m (r^2)-m (r^2-ε i))/ε i)
  let L : ℕ → ℝ := fun i ↦ A i + N i + D i
  have hAlim := graphBallOrientedCost_tendsto (c : Cover) hn hν hg hr he helim
  have hNlim := normalMeasure_sublevelCutoff_inner_tendsto μ (radialSquared_contDiff (c:=c)).continuous
    (radialSquared_periodic (c:=c)) he helim (r^2) hν
  have hDlim : Tendsto D atTop (𝓝 (K*(2*r)*d)) :=
    tendsto_const_nhds.mul (tendsto_backward_quotient_of_hasDerivAt hd he helim)
  have hlim : Tendsto L atTop (𝓝 (graphBallOrientedCost (c : Cover) n ν g r +
      (∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)) +
      K*(2*r)*d)) := (hAlim.add hNlim).add hDlim
  have hlocal (i : ℕ) (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff (radialSquared c) (r^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L i := by
    let w := radialDensityWeight (c : Cover) r (ε i)
    have hw : ContDiff ℝ (⊤ : ℕ∞) w := radialDensityWeight_contDiff _ _ _
    have hwc : HasCompactSupport w := radialDensityWeight_hasCompactSupport hr.le (he i)
    have hws : tsupport w ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
      radialDensityWeight_cell_support hr.le (by linarith) (he i)
    have hperiod : latticePeriodize w = sublevelCutoff (radialSquared c) (r^2) (ε i) :=
      radialDensityWeight_periodize hr.le hs (he i)
    have hf := integral_graphSublevel_relative_flux_le (c : Cover) hn hg hw hwc
      (fun x ↦ radialDensityWeight_nonneg _ _ _ x) ν hX
    rw [← interior_cutoff_flux_eq (c : Cover) n g hwc hws X,
      ← interior_cutoff_flux_eq (c : Cover) n g hwc hws (fun _ ↦ ν), hperiod] at hf
    have hdif := cutoff_constant_flux_sub_le hE hF
      (sublevelCutoff_contDiff (radialSquared_contDiff (c:=c)) (r^2) (ε i))
      (sublevelCutoff_periodic (radialSquared_periodic (c:=c)) (r^2) (ε i)) hν
    rw [cutoff_constant_flux_normal hE hμ
      (sublevelCutoff_contDiff (radialSquared_contDiff (c:=c)) (r^2) (ε i))
      (sublevelCutoff_periodic (radialSquared_periodic (c:=c)) (r^2) (ε i)) hν] at hdif
    have hgrad := sublevelCutoff_gradient_integral_le (hE.symmDiff hF) (radialSquared_contDiff (c:=c))
      (radialSquared_periodic (c:=c)) hK (norm_gradient_radialSquared hr.le hs.le) (he i)
    change _ ≤ A i + _ at hf
    change _ ≤ N i + _ at hdif
    change _ ≤ D i at hgrad
    dsimp only [L]
    linarith
  obtain ⟨hG,hb⟩ := perimeter_glued_local_flux_le hE hF hμ (radialSquared_contDiff (c:=c))
    (radialSquared_periodic (c:=c)) hK (norm_gradient_radialSquared hr.le hs.le) hd hlim hlocal
  have hdist : regionDistance E (gluedRegion E F (sublevelRegion (radialSquared c) (r^2))) =
      sublevelVolume (E ∆ F) (radialSquared c) (r^2) :=
    regionDistance_gluedRegion hE.nullMeasurableSet hF.nullMeasurableSet
      (measurableSet_sublevelRegion (radialSquared_contDiff (c:=c)).continuous.measurable _).nullMeasurableSet
  have hcomp := hc _ hG (hdist ▸ ht)
  rw [hdist] at hcomp
  rw [hμ.1] at hb
  rw [bundleOrientedExcess_eq]
  change _ ≤ graphBallOrientedCost (c : Cover) n ν g r + 2*K*(2*r)*d +
    C*sublevelVolume (E ∆ F) (radialSquared c) (r^2)
  linarith

lemma bundleOrientedExcess_mono (μ : FiniteMeasure NormalBundle) {ν : Cover}
    (hν : ‖ν‖ ≤ 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    (bundleOrientedExcess c) μ ν r ≤ (bundleOrientedExcess c) μ ν s := by
  have hi : Integrable (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hi.integrableOn
  · exact Eventually.of_forall fun z ↦ by
      have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
      exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν))
  · exact (show {z : NormalBundle | (radialSquared c) z.1 < r^2} ⊆ {z | (radialSquared c) z.1 < s^2} from
      fun z hz ↦ hz.trans_le (sq_le_sq₀ hr (hr.trans hrs) |>.mpr hrs)).eventuallyLE

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_oriented_interior_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ (p : Plane) (F : Set Torus), MeasurableSet F →
      ∀ a b B T K : ℝ, 0 < a → a < b → b < 1/4 → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ torusGraphRegion (c : Cover) n g ⊆ sublevelRegion (radialSquared c) (a^2) →
      sublevelVolume (E ∆ F) (radialSquared c) (b^2) < B →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (b^2) < T →
      (bundleOrientedExcess c) μ (graphSlopeNormal n p) a ≤
        (∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2)/2 +
          4*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_graph_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro c n hn g hg p F hF a b B T K ha hab hbs hT hK hchange he htotal
  let m := sublevelVolume (E ∆ F) (radialSquared c)
  have hm : Monotone m := sublevelVolume_mono _ _
  have ha2b2 : a^2 < b^2 := by nlinarith
  have hmb : m (b^2) < B := he
  have hmb0 : 0 ≤ m (b^2) := measureReal_nonneg
  have hB0 : 0 < B := hmb0.trans_lt hmb
  have hden : 0 < b^2-a^2 := sub_pos.mpr ha2b2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hden.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm ha2b2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hmt : m t < B := (hm ht.2.le).trans_lt hmb
  have hν : ‖graphSlopeNormal n p‖ ≤ 1 := (graphSlopeNormal_unit hn p).le
  have hderG := hasDerivAt_sublevelVolume_of_interior_change radialSquared_contDiff.continuous.measurable
    ht.1 hchange hd.hasDerivAt
  have htotρ : sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (ρ^2) < T :=
    (sublevelVolume_mono _ _ (by rw [hρsq]; exact ht.2.le)).trans_lt htotal
  have hcompare := hcomp c n hn (graphSlopeNormal n p) hν g hg ρ K (deriv m t) hρ0
    (hρb.trans hbs) hK (hρsq ▸ hderG) (htotρ.trans hT)
  have har := graphBallOrientedCost_le_disk (c : Cover) hn hg p ρ
  have henergy : (∫ y in Metric.ball (0 : Plane) ρ, ‖gradient g y-p‖^2) ≤
      ∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2 :=
    setIntegral_mono_set (smooth_graph_relative_energy_integrable hg p b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hρb.le).eventuallyLE
  have hmono := bundleOrientedExcess_mono (c:=c) μ hν ha.le hρa.le
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : 2*K*(2*ρ)*deriv m t ≤ 2*K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : 2*K*(2*ρ)*(B/(b^2-a^2)) ≤ 2*K*(2*b)*(B/(b^2-a^2)) := by
    gcongr
  have hc1 : C*sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left htotρ.le hC
  have heq : 4*K*b*B/(b^2-a^2) = 2*K*(2*b)*(B/(b^2-a^2)) := by ring
  rw [heq]
  linarith

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma torusGraphRegion_interior_symmDiff {n : Cover} (hn : ‖n‖ = 1)
    {f g : Plane → ℝ} {q H a : ℝ} (ha : 0 ≤ a) (has : a ≤ 1/4)
    (hmargin : q+H ≤ a)
    (he : ∀ y, q ≤ ‖y‖ → f y = g y)
    (hf : ∀ y, ‖y‖ < q → |f y| ≤ H)
    (hg : ∀ y, ‖y‖ < q → |g y| ≤ H) :
    torusGraphRegion (c : Cover) n f ∆ torusGraphRegion (c : Cover) n g ⊆
      sublevelRegion (radialSquared c) (a^2) := by
  intro z hz
  let v := representative z-(c : Cover)
  let y := normalPlaneCoordinates n v
  let t := ⟪n,v⟫
  have hz' : (t < f y ∧ ¬t < g y) ∨ (t < g y ∧ ¬t < f y) := hz
  have hy : ‖y‖ < q := by
    by_contra! hy
    have hh := he y hy
    rw [hh] at hz'
    rcases hz' with hz' | hz'
    · exact hz'.2 hz'.1
    · exact hz'.2 hz'.1
  have hf' := abs_le.mp (hf y hy)
  have hg' := abs_le.mp (hg y hy)
  have ht : |t| ≤ H := by
    rw [abs_le]
    rcases hz' with hz' | hz' <;> constructor <;> linarith
  have hv : ‖v‖ ≤ ‖y‖+|t| := by
    rw [← normalPlaneCoordinates_reconstruct hn v]
    exact (norm_add_le _ _).trans (by simp only [normalPlaneEmbedding_norm,norm_smul,
      Real.norm_eq_abs,hn,mul_one,y,t]; rfl)
  rw [sublevelRegion_radialSquared ha has]
  change dist (representative z) (c : Cover) < a
  rw [dist_eq_norm]
  change ‖v‖ < a
  linarith

lemma radial_sublevelVolume_le (E : Set Torus) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ 1/4) :
    sublevelVolume E (radialSquared c) (r^2) ≤ r^3*(Real.pi*4/3) := by
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared hr hrs]
  apply (measureReal_mono inter_subset_right).trans_eq
  rw [Measure.real,volume_cubeBall hr (by linarith),ENNReal.toReal_ofReal (by positivity)]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_scaled_graph_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (χ f u : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) f →
        ContDiff ℝ (⊤ : ℕ∞) u → ∀ (p : Plane →L[ℝ] ℝ) (r e m q h a b B K : ℝ),
      0 < r → 0 < e → 0 < a → a < b → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η →
      (∀ y, χ y ∈ Icc 0 1) → (∀ y, q ≤ ‖y‖ → χ y = 0) →
      (∀ y, ‖y‖ < q → |m+e*f y| ≤ h) → (∀ y, ‖y‖ < q → |m+e*u y| ≤ h) →
      q+h ≤ a → (∀ t, ‖deriv Real.smoothTransition t‖ ≤ K) →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n (graphRescale r e m f)) (radialSquared c) ((r*b)^2) < r^3*e^2*B →
      (bundleOrientedExcess c) μ (graphSlopeNormal n (e • (InnerProductSpace.toDual ℝ Plane).symm p)) (r*a) ≤
        r^2*e^2*((∫ y in Metric.ball (0 : Plane) b,
          ‖fderiv ℝ (graphBlend χ f u) y-p‖^2)/2+4*K*b*B/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_interior_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro c n hn χ f u hχ hf hu p r e m q h a b B K hr he ha hab hbs hsmall hχb hzero hfH huH hmargin hK hvol
  have hbpos : 0 < b := ha.trans hab
  let g := graphRescale r e m f
  let v := graphRescale r e m (graphBlend χ f u)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := graphRescale_contDiff hf r e m
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := graphRescale_contDiff (graphBlend_contDiff hχ hf hu) r e m
  have hnorm (y : Plane) : ‖r⁻¹ • y‖ = ‖y‖/r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    ring
  have hunchange (y : Plane) (hy : r*q ≤ ‖y‖) : g y = v y := by
    have hz : χ (r⁻¹ • y) = 0 := hzero _ (by rw [hnorm,le_div_iff₀ hr]; nlinarith)
    simp only [g,v,graphRescale,graphBlend_eq_of_zero hz]
  have hgH (y : Plane) (hy : ‖y‖ < r*q) : |g y| ≤ r*h := by
    dsimp [g,graphRescale]
    rw [abs_mul,abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left (hfH _ _) hr.le
    rw [hnorm,div_lt_iff₀ hr]
    nlinarith
  have hvH (y : Plane) (hy : ‖y‖ < r*q) : |v y| ≤ r*h := by
    have hyr : ‖r⁻¹ • y‖ < q := by rw [hnorm,div_lt_iff₀ hr]; nlinarith
    have heq : m+e*graphBlend χ f u (r⁻¹ • y) =
        graphBlend χ (fun y ↦ m+e*f y) (fun y ↦ m+e*u y) (r⁻¹ • y) := by
      simp only [graphBlend]
      ring
    dsimp [v,graphRescale]
    rw [abs_mul,abs_of_pos hr,heq]
    exact mul_le_mul_of_nonneg_left (graphBlend_abs_le (hχb _) (hfH _ hyr) (huH _ hyr)) hr.le
  have hra : 0 < r*a := mul_pos hr ha
  have hrab : r*a < r*b := mul_lt_mul_of_pos_left hab hr
  have hsupp : torusGraphRegion (c : Cover) n g ∆ torusGraphRegion (c : Cover) n v ⊆
      sublevelRegion (radialSquared c) ((r*a)^2) :=
    torusGraphRegion_interior_symmDiff hn hra.le (hrab.le.trans hbs.le)
      (by nlinarith [mul_le_mul_of_nonneg_left hmargin hr.le]) hunchange hgH hvH
  have htot : sublevelVolume (E ∆ torusGraphRegion (c : Cover) n v) (radialSquared c) ((r*b)^2) <
      (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hbs.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hh := hcomp c n hn v hv (e • (InnerProductSpace.toDual ℝ Plane).symm p)
    (torusGraphRegion (c : Cover) n g) (measurableSet_torusGraphRegion _ _ hg.continuous)
    (r*a) (r*b) (r^3*e^2*B) ((r*b)^3*(Real.pi*8/3)) K hra hrab hbs hsmall hK hsupp hvol htot
  have heq : e • (InnerProductSpace.toDual ℝ Plane).symm p =
      (InnerProductSpace.toDual ℝ Plane).symm (e • p) := by simp only [map_smul]
  rw [heq] at hh ⊢
  simp_rw [plane_relative_gradient_norm] at hh
  dsimp only [v] at hh
  rw [graphRescale_relative_energy (graphBlend_contDiff hχ hf hu) hr] at hh
  apply hh.trans_eq
  have hd : b^2-a^2 ≠ 0 := by nlinarith
  field_simp

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_sequential_oriented_decay_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → InteriorCenter) (r e m h B : ℕ → ℝ) (n : ℕ → Cover) (f : ℕ → Plane → ℝ)
    (hr : ∀ i, 0 < r i) (he : ∀ i, 0 < e i) (hn : ∀ i, ‖n i‖ = 1)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hrlim : Tendsto r atTop (𝓝 0)) (helim : Tendsto e atTop (𝓝 0))
    (hmlim : Tendsto m atTop (𝓝 0)) (hhlim : Tendsto h atTop (𝓝 0))
    (hBlim : Tendsto B atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (p : Plane →L[ℝ] ℝ) {A H : ℝ} (hA : 0 ≤ A)
    (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
    (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
    (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
    (hheight : ∀ i y, ‖y‖ < 2*θ → |m i+e i*f i y| ≤ h i)
    (hmismatch : ∀ i,
      sublevelVolume (E ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
        (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
        (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
      (r (ψ i))^2*(e (ψ i))^2*(2*H+ε) := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_scaled_graph_comparison hV hE hmin hμ
  obtain ⟨s,q,a,b,D,χ,ψ,hs,hsq,hqa,hab,hb,hψ,hχ,hD,hd,hχb,hone,hzero,hblend⟩ :=
    strong_L2_annulus_replacement hθ f hf hu p hA henergy hH hconv hε
  have ha : 0 < a := (hθ.trans_le hs).trans (hsq.trans hqa)
  have hbpos : 0 < b := ha.trans hab
  have hH0 : 0 ≤ H := (integral_nonneg fun y ↦ sq_nonneg _).trans hH
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0 : Plane) (2*θ)).exists_bound_of_continuousOn hu.continuous.continuousOn
  let M := max M₀ 0
  have hM (y : Plane) (hy : ‖y‖ < q) : |u y| ≤ M := by
    apply (hM₀ y ?_).trans (le_max_left _ _)
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (hy.trans (hqa.trans hab)).le.trans hb
  let height : ℕ → ℝ := fun i ↦ max (h i) (|m i|+e i*M)
  have hheightlim : Tendsto height atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul,zero_add,max_self] using hhlim.max (hmlim.abs.add (helim.mul_const M))
  obtain ⟨K,hKpos,hK⟩ := smoothTransition_exists_deriv_bound
  have hrblim : Tendsto (fun i ↦ r (ψ i)*b) atTop (𝓝 0) := by
    simpa using (hrlim.comp hψ.tendsto_atTop).mul_const b
  have hvlim : Tendsto (fun i ↦ (r (ψ i)*b)^3*(Real.pi*8/3)) atTop (𝓝 0) := by
    simpa using (hrblim.pow 3).mul_const (Real.pi*8/3)
  have herrlim : Tendsto (fun i ↦ 4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div,zero_add,Function.comp_def] using
      (((hBlim.comp hψ.tendsto_atTop).const_mul (4*K*b)).div_const (b^2-a^2)).add
        ((hrel.comp hψ.tendsto_atTop).const_mul (C*b^3))
  refine ⟨ψ,hψ,?_⟩
  filter_upwards [hblend,
    hrblim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hvlim.eventually (gt_mem_nhds hη),
    (hheightlim.comp hψ.tendsto_atTop).eventually (gt_mem_nhds (sub_pos.mpr hqa)),
    herrlim.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with i hblend hbs hsmall hmargin herr
  dsimp only [Function.comp_def] at hmargin
  have hfheight (y : Plane) (hy : ‖y‖ < q) : |m (ψ i)+e (ψ i)*f (ψ i) y| ≤ height (ψ i) :=
    (hheight _ _ ((hy.trans (hqa.trans hab)).trans_le hb)).trans (le_max_left _ _)
  have huheight (y : Plane) (hy : ‖y‖ < q) : |m (ψ i)+e (ψ i)*u y| ≤ height (ψ i) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos (he _)]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hM y hy) (he _).le)).trans (le_max_right _ _)
  have hvol : sublevelVolume
      (E ∆ torusGraphRegion (c (ψ i) : Cover) (n (ψ i)) (graphRescale (r (ψ i)) (e (ψ i)) (m (ψ i)) (f (ψ i))))
      (radialSquared (c (ψ i))) ((r (ψ i)*b)^2) < (r (ψ i))^3*(e (ψ i))^2*B (ψ i) := by
    apply (sublevelVolume_mono _ _ ?_).trans_lt (hmismatch _)
    apply (sq_le_sq₀ (mul_nonneg (hr _).le hbpos.le) (mul_nonneg (hr _).le (by positivity))).mpr
    exact mul_le_mul_of_nonneg_left hb (hr _).le
  have hh := hcomp (c (ψ i)) (n (ψ i)) (hn _) χ (f (ψ i)) u hχ (hf _) hu p
    (r (ψ i)) (e (ψ i)) (m (ψ i)) q (height (ψ i)) a b (B (ψ i)) K
    (hr _) (he _) ha hab hbs hsmall hχb hzero hfheight huheight (by linarith) hK hvol
  have heq : (r (ψ i))^2*(e (ψ i))^2*
      ((∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
        4*K*b*B (ψ i)/(b^2-a^2))+C*(r (ψ i)*b)^3 =
      (r (ψ i))^2*(e (ψ i))^2*
        ((∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
          (4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2))) := by
    field_simp [(he (ψ i)).ne']
    ring
  rw [heq] at hh
  have hinside : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
      (4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2)) ≤ 2*H+ε := by linarith
  have hmono := bundleOrientedExcess_mono (c:=c (ψ i)) μ
    (graphSlopeNormal_unit (hn (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)).le
    (mul_nonneg (hr (ψ i)).le hθ.le)
    (mul_le_mul_of_nonneg_left (hs.trans (hsq.le.trans hqa.le)) (hr (ψ i)).le)
  exact hmono.trans (hh.trans (mul_le_mul_of_nonneg_left hinside (by positivity)))

end CubicTorus.MovingCenter

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay_oai := @OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay_oai
