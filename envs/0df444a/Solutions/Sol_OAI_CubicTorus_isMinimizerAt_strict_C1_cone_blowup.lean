-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:14:30.068856+00:00
-- url     : https://prove2.me/submissions/4e85ad97-b966-42c9-bb26-4e397fe7f70a

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_primary_offvertex_C1
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_density_pos
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_paired_blowup

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma setIntegral_characteristic {E : Set Torus} (hE : MeasurableSet E) (s : Set Torus)
    (_hs : MeasurableSet s) :
    (∫ x in s, characteristic E x ∂torusVolume) = torusVolume.real (E ∩ s) := by
  change (∫ x in s, E.indicator (fun _ ↦ (1 : ℝ)) x ∂torusVolume) = _
  rw [integral_indicator hE, Measure.restrict_restrict hE,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

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
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radialDensityWeight_cell_support {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/2) (hε : 0 < ε) :
    tsupport (radialDensityWeight cubeCenter r ε) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := radialDensityWeight_tsupport hr hε hx
  have hd : ‖x-cubeCenter‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
  have hi := (PiLp.norm_apply_le (x-cubeCenter) i).trans hd
  change ‖x i - (1/2 : ℝ)‖ ≤ r at hi
  rw [Real.norm_eq_abs, abs_le] at hi
  constructor <;> linarith

lemma radialDensityWeight_periodize {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/4) (hε : 0 < ε) :
    latticePeriodize (radialDensityWeight cubeCenter r ε) = sublevelCutoff radialSquared (r^2) ε := by
  funext x
  rw [← periodic_representative (latticePeriodize_periodic _) x,
    ← periodic_representative (sublevelCutoff_periodic radialSquared_periodic (r^2) ε) x]
  let z := representative (quotientMap x)
  have hz : z ∈ fundamentalCube := representative_mem_fundamentalCube _
  rw [(latticePeriodize_eventuallyEq (radialDensityWeight_hasCompactSupport hr hε)
    (radialDensityWeight_cell_support hr (by linarith) hε)
    (fun i ↦ ⟨(hz i).1, (hz i).2.le⟩)).eq_of_nhds]
  change radialDensityWeight cubeCenter r ε z = sublevelCutoff radialSquared (r^2) ε z
  by_cases hz' : ‖z-cubeCenter‖ < r
  · have he := (radialSquared_eventuallyEq_norm_sq (hz'.trans hs)).eq_of_nhds
    simp only [radialDensityWeight, sublevelCutoff, he]
  · have hh : ¬ radialSquared z < r^2 := by
      rw [radialSquared_sublevel_iff hz (by nlinarith)]
      have hb : r ≤ ‖z-cubeCenter‖ := le_of_not_gt hz'
      nlinarith [norm_nonneg (z-cubeCenter)]
    rw [radialDensityWeight_zero hr hε (le_of_not_gt hz')]
    exact (Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt hh)) hε.le)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma normalMeasure_radial_sublevel (μ : FiniteMeasure NormalBundle) {r : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1/4) :
    (μ : Measure NormalBundle).real {z | radialSquared z.1 < r^2} =
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) r) := by
  rw [← cubeBall_eq_metricBall, ← sublevelRegion_radialSquared hr hs]
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle)
    (sublevelRegion radialSquared (r^2))).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable
    (measurableSet_sublevelRegion radialSquared_contDiff.continuous.measurable _)]
  congr 1
  ext z
  exact (mem_sublevelRegion_quotient radialSquared_periodic (r^2) z.1).symm

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVAnnulusSelection
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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radial_sublevelVolume_le (E : Set Torus) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ 1/4) :
    sublevelVolume E radialSquared (r^2) ≤ r^3*(Real.pi*4/3) := by
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared hr hrs]
  apply (measureReal_mono inter_subset_right).trans_eq
  rw [Measure.real,volume_cubeBall hr (by linarith),ENNReal.toReal_ofReal (by positivity)]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_BVColumnMismatchMeasure
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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
namespace CubicTorus

lemma characteristic_symmDiff_eq_abs (U F : Set Torus) (x : Torus) :
    characteristic (U ∆ F) x = |characteristic U x-characteristic F x| := by
  by_cases hU : x ∈ U <;> by_cases hF : x ∈ F <;>
    simp [characteristic, Set.mem_symmDiff, hU, hF]

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_blowupNormalMap (c : Cover) (r : ℝ) :
    Continuous (blowupNormalMap c r) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

lemma blowupNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : NormalBundle) :
    (blowupNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [blowupNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_divergence_le_coverLocalPerimeter {A O : Set Cover} {L : ℝ}
    (hL : coverLocalPerimeter A O ≤ ENNReal.ofReal L) (hL0 : 0 ≤ L)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) ≤ L := by
  apply (ENNReal.ofReal_le_ofReal_iff hL0).mp
  have hh : ENNReal.ofReal (∫ x in A, divergence F x) ≤ coverLocalPerimeter A O :=
    le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
      (le_iSup_of_le hO (le_iSup_of_le hb le_rfl))))
  exact hh.trans hL

theorem coverLocalPerimeter_le_normal {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle} (hO : MeasurableSet O)
    (hO1 : O ⊆ Metric.closedBall (0 : Cover) 1)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter A O ≤ (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hFO
  apply iSup_le
  intro hb
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} := hO.preimage measurable_fst
  have hc : Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) :=
    (continuous_subtype_val.comp continuous_snd).inner (hF.continuous.comp continuous_fst)
  have hbd (z : BlowupNormalBundle) : ‖⟪(z.2 : Cover),F z.1⟫‖ ≤ 1 := by
    calc
      _ ≤ ‖(z.2 : Cover)‖*‖F z.1‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by rw [z.2.property,one_mul]; exact hb _
  have hi : Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) ν :=
    Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ hbd)
  have hri : Integrable ({z : BlowupNormalBundle | z.1 ∈ O}.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const 1).indicator hm
  have he : (∫ x in A, divergence F x) ≤ (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ O} := by
    rw [← hflux F hF (hFO.trans hO1)]
    have hh := integral_mono_ae hi hri (ae_of_all _ fun z ↦ ?_)
    · simpa only [integral_indicator hm,integral_const,smul_eq_mul,mul_one,
        measureReal_restrict_apply_univ] using hh
    · by_cases hz : z.1 ∈ O
      · simpa [Set.indicator,hz] using (le_abs_self _).trans (hbd z)
      · have hzero : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hFO hh))
        simp [Set.indicator,hz,hzero]
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVLocalScaling
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

lemma measurableSet_affineCoverRegion {A : Set Cover} (hA : MeasurableSet A) (c : Cover) (r : ℝ) :
    MeasurableSet (affineCoverRegion A c r) := hA.preimage (by fun_prop)

lemma divergence_affine_pullback {F : Cover → Cover} (hF : Differentiable ℝ F)
    (c : Cover) (r : ℝ) (x : Cover) :
    divergence (fun y : Cover ↦ F (r • y+c)) x = r*divergence F (r • x+c) := by
  have hd := (hF (r • x+c)).hasFDerivAt.comp x (((hasFDerivAt_id x).const_smul r).add_const c)
  change HasFDerivAt (fun y : Cover ↦ F (r • y+c)) _ x at hd
  simp only [divergence,hd.fderiv,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,PiLp.smul_apply,
    smul_eq_mul,Finset.mul_sum]

lemma tsupport_affine_pullback {F : Cover → Cover} (c : Cover) {r : ℝ} (hr : 0 < r)
    {b : ℝ} (hs : tsupport F ⊆ Metric.closedBall c (r*b)) :
    tsupport (fun y : Cover ↦ F (r • y+c)) ⊆ Metric.closedBall (0 : Cover) b := by
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage F
    (by fun_prop : Continuous (fun y : Cover ↦ r • y+c)) hx)
  have hh' : r*‖x‖ ≤ r*b := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_right,norm_smul,
      Real.norm_of_nonneg hr.le] using hh
  simpa only [Metric.mem_closedBall,dist_zero_right] using (mul_le_mul_iff_right₀ hr).mp hh'

lemma integral_divergence_affineCoverRegion {A : Set Cover} (hA : MeasurableSet A)
    (c : Cover) {r : ℝ} (hr : 0 < r) {F : Cover → Cover} (hF : Differentiable ℝ F) :
    (∫ x in affineCoverRegion A c r, divergence F x) =
      r^2*(∫ x in A, divergence (fun y : Cover ↦ F (r • y+c)) x) := by
  have hAr := measurableSet_affineCoverRegion hA c r
  have he := integral_cover_affine_scaling
    ((affineCoverRegion A c r).indicator (divergence F)) c hr
  have hind : (fun y : Cover ↦ (affineCoverRegion A c r).indicator (divergence F) (r • y+c)) =
      A.indicator (fun y ↦ divergence F (r • y+c)) := by
    funext y
    have hm : r • y+c ∈ affineCoverRegion A c r ↔ y ∈ A := by
      simp only [affineCoverRegion,mem_ofPred_eq,add_sub_cancel_right,smul_smul,
        inv_mul_cancel₀ hr.ne',one_smul]
    by_cases hy : y ∈ A <;> simp [hm,hy]
  rw [integral_indicator hAr,hind,integral_indicator hA] at he
  rw [he]
  simp_rw [divergence_affine_pullback hF c r]
  rw [integral_const_mul]
  ring

theorem affineCoverRegion_flux_le {A : Set Cover} (hA : MeasurableSet A)
    {L b : ℝ} (hL0 : 0 ≤ L)
    (hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (c : Cover) {r : ℝ} (hr : 0 < r) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : tsupport F ⊆ Metric.closedBall c (r*b))
    (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in affineCoverRegion A c r, divergence F x) ≤ r^2*L := by
  rw [integral_divergence_affineCoverRegion hA c hr (hF.differentiable (by simp))]
  have hFs := tsupport_affine_pullback c hr hs
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  exact integral_divergence_le_coverLocalPerimeter hL hL0
    (hF.comp ((contDiff_id.const_smul r).add contDiff_const))
    ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hFs)
    hFs (fun x ↦ hb _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma measurableSet_torusCoverRegion {A : Set Cover} (hA : MeasurableSet A) :
    MeasurableSet (torusCoverRegion A) := hA.preimage measurable_representative

lemma characteristic_torusCoverRegion {x : Cover} (hx : x ∈ fundamentalCube) (A : Set Cover) :
    characteristic (torusCoverRegion A) (quotientMap x) = A.indicator (fun _ ↦ (1 : ℝ)) x := by
  have hm : quotientMap x ∈ torusCoverRegion A ↔ x ∈ A := by
    change representative (quotientMap x) ∈ A ↔ x ∈ A
    rw [representative_quotientMap_of_mem hx]
  by_cases ha : x ∈ A <;> simp [characteristic,Set.indicator,hm,ha]

lemma interior_cutoff_flux_eq_set {A : Set Cover} (hA : MeasurableSet A)
    {w : Cover → ℝ} (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (X : Cover → Cover) :
    (∫ x in fundamentalCube, characteristic (torusCoverRegion A) (quotientMap x) *
      divergence (fun y ↦ latticePeriodize w y • X y) x) =
      ∫ x in A, divergence (fun y ↦ w y • X y) x := by
  rw [← integral_indicator measurableSet_fundamentalCube,← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · rw [indicator_of_mem hx,characteristic_torusCoverRegion hx]
    have he := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩)).smul
      (EventuallyEq.rfl : X =ᶠ[𝓝 x] X)
    have hd := he.fderiv_eq (𝕜 := ℝ)
    have hdiv : divergence (fun y ↦ latticePeriodize w y • X y) x =
        divergence (fun y ↦ w y • X y) x := by simp only [divergence,hd]
    rw [hdiv]
    by_cases ha : x ∈ A <;> simp [Set.indicator,ha]
  · rw [indicator_of_notMem hx]
    have hsup : tsupport (fun y ↦ w y • X y) ⊆ tsupport w := tsupport_smul_subset_left w X
    have hdiv : divergence (fun y ↦ w y • X y) x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      exact hx (fun i ↦ ⟨(hs (hsup hh) i).1.le,(hs (hsup hh) i).2⟩)
    by_cases ha : x ∈ A <;> simp [Set.indicator,ha,hdiv]

lemma torus_affine_radial_flux_le {A : Set Cover} (hA : MeasurableSet A)
    {L b r ρ ε : ℝ} (hL0 : 0 ≤ L)
    (hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hρb : ρ ≤ r*b) (hρs : ρ < 1/4) (hε : 0 < ε)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x in fundamentalCube,
      characteristic (torusCoverRegion (affineCoverRegion A cubeCenter r)) (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) ε y • X y) x) ≤ r^2*L := by
  rw [← radialDensityWeight_periodize hρ hρs hε,
    interior_cutoff_flux_eq_set (measurableSet_affineCoverRegion hA _ _)
      (radialDensityWeight_hasCompactSupport hρ hε)
      (radialDensityWeight_cell_support hρ (by linarith) hε)]
  apply affineCoverRegion_flux_le hA hL0 hL cubeCenter hr
    ((radialDensityWeight_contDiff _ _ _).smul hX.1)
  · exact (tsupport_smul_subset_left _ _).trans
      ((radialDensityWeight_tsupport hρ hε).trans (Metric.closedBall_subset_closedBall hρb))
  · intro x
    change ‖radialDensityWeight cubeCenter ρ ε x • X x‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact (mul_le_of_le_one_right (radialDensityWeight_nonneg _ _ _ _) (hX.2.2 x)).trans
      (radialDensityWeight_le_one _ _ _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma torus_affine_symmDiff_support {A B : Set Cover} {a r : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hs : r*a ≤ 1/4)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    torusCoverRegion (affineCoverRegion A cubeCenter r) ∆
      torusCoverRegion (affineCoverRegion B cubeCenter r) ⊆
        sublevelRegion radialSquared ((r*a)^2) := by
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le ha) hs]
  intro z hz
  have hm : r⁻¹ • (representative z-cubeCenter) ∈ A ∆ B := hz
  have hh := hAB hm
  have hh' : ‖representative z-cubeCenter‖/r < a := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hh
  change dist (representative z) cubeCenter < r*a
  rw [dist_eq_norm]
  simpa only [mul_comm] using (div_lt_iff₀ hr).mp hh'

lemma torus_affine_symmDiff_volume {E : Set Torus} (hE : MeasurableSet E)
    {A : Set Cover} (hA : MeasurableSet A) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hs : r*b ≤ 1/4) :
    sublevelVolume (E ∆ torusCoverRegion (affineCoverRegion A cubeCenter r))
      radialSquared ((r*b)^2) =
      r^3*(∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E cubeCenter r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) := by
  let F := torusCoverRegion (affineCoverRegion A cubeCenter r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hc : Metric.ball cubeCenter (r*b) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior (by linarith))
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le hb) hs,cubeBall_eq_metricBall,
    ← setIntegral_characteristic (hE.symmDiff hF) _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball (characteristic (E ∆ F)) (measurable_characteristic (hE.symmDiff hF))
      cubeCenter (r*b) hc,
    integral_ball_affine_scaling _ cubeCenter hr b]
  congr 1
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x hx
  have hxb : cubeCenter+r • x ∈ Metric.ball cubeCenter (r*b) := by
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,
      Real.norm_of_nonneg hr.le] using (mul_lt_mul_of_pos_left (show ‖x‖ < b by simpa only [Metric.mem_ball,dist_zero_right] using hx) hr)
  have hxc : cubeCenter+r • x ∈ fundamentalCube := fun j ↦ ⟨(hc hxb j).1.le,(hc hxb j).2⟩
  dsimp only
  rw [characteristic_symmDiff_eq_abs]
  dsimp only [F]
  rw [characteristic_torusCoverRegion hxc]
  have hm : cubeCenter+r • x ∈ affineCoverRegion A cubeCenter r ↔ x ∈ A := by
    simp only [affineCoverRegion,Set.mem_ofPred_eq,add_sub_cancel_left,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  change |blowupCharacteristic E cubeCenter r x-_| = _
  by_cases ha : x ∈ A <;> simp [Set.indicator,hm,ha]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_local_flux_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (F : Set Torus), MeasurableSet F →
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x+latticeVector n) = q x) →
      ∀ K M t d L : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume (E ∆ F) q) d t →
      sublevelVolume (E ∆ F) q t < η →
      (∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
        (∫ x in fundamentalCube, characteristic F (quotientMap x)*
          divergence (fun y ↦ sublevelCutoff q t (1/((i : ℝ)+1)) y • X y) x) ≤ L) →
      (μ : Measure NormalBundle).real {z | q z.1 < t} ≤ L+K*M*d+C*sublevelVolume (E ∆ F) q t := by
  obtain ⟨η,C,hη,hC,hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η,C,hη,hC,?_⟩
  intro F hF q hq hp K M t d L hK hg hd ht hloc
  obtain ⟨hG,hbound⟩ := perimeter_glued_local_flux_le hE hF hμ hq hp hK hg hd
    (tendsto_const_nhds (f := atTop) (x := L)) hloc
  have he : regionDistance E (gluedRegion E F (sublevelRegion q t)) =
      sublevelVolume (E ∆ F) q t := regionDistance_gluedRegion hE.nullMeasurableSet
        hF.nullMeasurableSet (measurableSet_sublevelRegion hq.continuous.measurable _).nullMeasurableSet
  have hh := hc _ hG (he ▸ ht)
  rw [he] at hh
  rw [hμ.1] at hbound
  linarith

theorem isMinimizerAt_local_flux_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ F G : Set Torus,
      MeasurableSet F → MeasurableSet G → ∀ a b B T K L : ℝ,
      0 < a → a < b → b < 1/4 → 0 ≤ L → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ G ⊆ sublevelRegion radialSquared (a^2) →
      sublevelVolume (E ∆ G) radialSquared (b^2) < B →
      sublevelVolume (E ∆ F) radialSquared (b^2) < T →
      (∀ ρ ∈ Ioo a b, ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
        (∫ x in fundamentalCube, characteristic F (quotientMap x)*
          divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L) →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) a) ≤
        L+2*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro F G hF hG a b B T K L ha hab hbs hL hT hK hFG heG heF hloc
  let m := sublevelVolume (E ∆ G) radialSquared
  have hm : Monotone m := sublevelVolume_mono _ _
  have hab2 : a^2 < b^2 := by nlinarith
  have hB : 0 < B := (show 0 ≤ m (b^2) from measureReal_nonneg).trans_lt heG
  have hdpos : 0 < b^2-a^2 := sub_pos.mpr hab2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hdpos.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm hab2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hdF : HasDerivAt (sublevelVolume (E ∆ F) radialSquared) (deriv m t) t := by
    exact hasDerivAt_sublevelVolume_of_interior_change
      radialSquared_contDiff.continuous.measurable ht.1
      (by simpa only [symmDiff_comm] using hFG) hd.hasDerivAt
  have hFt : sublevelVolume (E ∆ F) radialSquared t < T :=
    (sublevelVolume_mono _ _ ht.2.le).trans_lt heF
  have hh := hcomp F hF radialSquared radialSquared_contDiff radialSquared_periodic
    K (2*ρ) (ρ^2) (deriv m t) L hK (norm_gradient_radialSquared hρ0.le (hρb.trans hbs).le)
    (hρsq ▸ hdF) (by rw [hρsq]; exact hFt.trans hT) (hloc ρ ⟨hρa,hρb⟩)
  rw [normalMeasure_radial_sublevel μ hρ0.le (hρb.trans hbs).le] at hh
  have hmono : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) a) ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) ρ) :=
    measureReal_mono (Metric.ball_subset_ball hρa.le)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : K*(2*ρ)*deriv m t ≤ K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : K*(2*ρ)*(B/(b^2-a^2)) ≤ K*(2*b)*(B/(b^2-a^2)) := by gcongr
  have hct : C*sublevelVolume (E ∆ F) radialSquared (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left (by rw [hρsq]; exact hFt.le) hC
  have heq : K*(2*b)*(B/(b^2-a^2)) = 2*K*b*B/(b^2-a^2) := by ring
  rw [heq] at hd2
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_scaled_set_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ A B : Set Cover,
      MeasurableSet A → MeasurableSet B → ∀ a b L K r δ : ℝ,
      0 < a → a < b → 0 < r → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η → 0 ≤ L →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L →
      A ∆ B ⊆ Metric.ball (0 : Cover) a →
      (∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E cubeCenter r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < δ →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) (r*a)) ≤
        r^2*(L+2*K*b*δ/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro A B hA hB a b L K r δ ha hab hr hsmall hηr hL hK hper hAB herr
  let F := torusCoverRegion (affineCoverRegion B cubeCenter r)
  let G := torusCoverRegion (affineCoverRegion A cubeCenter r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hB _ _)
  have hG : MeasurableSet G := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hbpos : 0 < b := ha.trans hab
  have hra : 0 < r*a := mul_pos hr ha
  have hrab : r*a < r*b := mul_lt_mul_of_pos_left hab hr
  have hchange : F ∆ G ⊆ sublevelRegion radialSquared ((r*a)^2) :=
    torus_affine_symmDiff_support hr ha.le (hrab.le.trans hsmall.le)
      (by simpa only [symmDiff_comm] using hAB)
  have hvol : sublevelVolume (E ∆ G) radialSquared ((r*b)^2) < r^3*δ := by
    rw [torus_affine_symmDiff_volume hE hA hr (ha.trans hab).le hsmall.le]
    exact mul_lt_mul_of_pos_left herr (pow_pos hr 3)
  have htot : sublevelVolume (E ∆ F) radialSquared ((r*b)^2) < (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hsmall.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hloc : ∀ ρ ∈ Ioo (r*a) (r*b), ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
      (∫ x in fundamentalCube, characteristic F (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ r^2*L := by
    intro ρ hρ i X hX
    exact torus_affine_radial_flux_le hB hL hper hr (hra.trans hρ.1).le hρ.2.le
      (hρ.2.trans hsmall) (by positivity) hX
  have hh := hcomp F G hF hG (r*a) (r*b) (r^3*δ) ((r*b)^3*(Real.pi*8/3)) K (r^2*L)
    hra hrab hsmall (mul_nonneg (sq_nonneg _) hL) hηr hK hchange hvol htot hloc
  apply hh.trans_eq
  have hd : b^2-a^2 ≠ 0 := by nlinarith
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma density_scaled_mass_tendsto {m : ℝ → ℝ} {θ : ℝ}
    (hθ : Tendsto (fun t ↦ m t/t^2) (𝓝[>] 0) (𝓝 θ))
    {l : Filter ℕ} (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r l (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i ↦ m (r i*a)/(r i)^2) l (𝓝 (θ*a^2)) := by
  have ht : Tendsto (fun i ↦ r i*a) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const a,
      Eventually.of_forall fun i ↦ mul_pos (hr i) ha⟩
  have hh := (hθ.comp ht).mul_const (a^2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',ha.ne']

lemma blowup_error_integrable {E : Set Torus} (hE : MeasurableSet E)
    {A : Set Cover} (hA : MeasurableSet A) (c : Cover) (r R : ℝ) :
    IntegrableOn (fun x ↦ |blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      (Metric.closedBall (0 : Cover) R) := by
  have hAi : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hA
  apply Integrable.of_bound (((measurable_blowupCharacteristic hE c r).sub hAi).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_abs]
  have hB : |A.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [Set.indicator,hx]
  exact (abs_sub _ _).trans (by linarith [blowupCharacteristic_bound E c r x])

theorem isMinimizerAt_blowup_competitor_bound {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0))
    {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b ≤ R) (hL : 0 ≤ L)
    (hper : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) : θ*a^2 ≤ L := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_scaled_set_replacement hV hE hmin hμ
  obtain ⟨K,hKpos,hK⟩ := smoothTransition_exists_deriv_bound
  let D : ℕ → ℝ := fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
    |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|
  have hsmall : ∀ᶠ i in atTop, r i*b < 1/4 ∧ (r i*b)^3*(Real.pi*8/3) < η := by
    have hs1 : Tendsto (fun i ↦ r i*b) atTop (𝓝 0) := by simpa using hrlim.mul_const b
    have hs2 : Tendsto (fun i ↦ (r i*b)^3*(Real.pi*8/3)) atTop (𝓝 0) := by
      simpa using (hs1.pow 3).mul_const (Real.pi*8/3)
    exact (hs1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).and
      (hs2.eventually (gt_mem_nhds hη))
  have hineq : ∀ᶠ i in atTop,
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) (r i*a))/(r i)^2 ≤
        L+2*K*b*(D i+r i)/(b^2-a^2)+C*r i*b^3 := by
    filter_upwards [hsmall] with i hi
    have herr : (∫ x in Metric.ball (0 : Cover) b,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < D i+r i := by
      have hm := setIntegral_mono_set (blowup_error_integrable hE hA cubeCenter (r i) R)
        (ae_of_all _ fun x ↦ abs_nonneg _)
        ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)).eventuallyLE)
      dsimp only [D]
      exact lt_of_le_of_lt hm (lt_add_of_pos_right _ (hr i))
    have hh := hcomp A B hA hB a b L K (r i) (D i+r i) ha hab (hr i) hi.1 hi.2 hL hK hper hAB herr
    apply (div_le_iff₀ (sq_pos_of_pos (hr i))).mpr
    apply hh.trans_eq
    ring
  have hm := density_scaled_mass_tendsto hθ r hr hrlim ha
  have hlim : Tendsto (fun i ↦ L+2*K*b*(D i+r i)/(b^2-a^2)+C*r i*b^3) atTop (𝓝 L) := by
    have hh := ((tendsto_const_nhds (x := L)).add
      (((tendsto_const_nhds (x := 2*K*b)).mul (hconv.add hrlim)).div_const (b^2-a^2))).add
        (((tendsto_const_nhds (x := C)).mul hrlim).mul_const (b^3))
    simpa only [zero_add,mul_zero,zero_mul,zero_div,add_zero] using hh
  exact le_of_tendsto_of_tendsto hm hlim hineq

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

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVConeSecondaryFlux
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_radial_smul {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ) (x : Cover) :
    divergence (fun y ↦ ψ y • y) x = 3*ψ x+fderiv ℝ ψ x x := by
  change divergence (fun y ↦ ψ y • id y) x = _
  rw [divergence_smul_function (hψ x) differentiableAt_id,inner_gradient_left]
  simp only [id_eq]
  have hd : divergence (id : Cover → Cover) x = 3 := by
    unfold divergence
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
    norm_num [Fin.sum_univ_three]
  rw [hd]
  ring

theorem limit_set_radial_flux {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    (hrad : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
      ⟪(z.2 : Cover),z.1⟫ = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ψ x • x) := hψ.smul contDiff_id
  have hFs : tsupport (fun x ↦ ψ x • x) ⊆ Metric.closedBall (0 : Cover) 1 :=
    (tsupport_smul_subset_left ψ (fun x : Cover ↦ x)).trans (hs.trans Metric.ball_subset_closedBall)
  have he := hflux _ hF hFs
  have hz : (∫ z : BlowupNormalBundle, ⟪(z.2 : Cover),ψ z.1 • z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hrad] with z hz
    change ⟪(z.2 : Cover),ψ z.1 • z.1⟫ = 0
    by_cases hx : z.1 ∈ Metric.ball (0 : Cover) 1
    · rw [inner_smul_right,hz hx,mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh)),zero_smul,inner_zero_right]
  rw [hz] at he
  simpa only [divergence_radial_smul (hψ.differentiable (by simp))] using he.symm

lemma hasDerivAt_setIntegral_dilation {A : Set Cover} (hA : MeasurableSet A)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (s • x))
      (∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (t • x) x) t := by
  let η : Measure Cover := volume.restrict (A ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hψ.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  have hm (s : ℝ) : AEStronglyMeasurable (fun x ↦ ψ (s • x)) η := by
    have hc : Continuous (fun x : Cover ↦ s • x) := by fun_prop
    exact (hψ.continuous.comp hc).aestronglyMeasurable
  have hi : Integrable (fun x ↦ ψ (t • x)) η :=
    Integrable.of_bound (hm t) M (ae_of_all _ (fun x ↦ hM _))
  have hm' : AEStronglyMeasurable (fun x ↦ fderiv ℝ ψ (t • x) x) η := by
    have hc : Continuous (fun x : Cover ↦ t • x) := by fun_prop
    exact (((hψ.continuous_fderiv (by simp)).comp hc).clm_apply
      continuous_id).aestronglyMeasurable
  have hb : ∀ᵐ x ∂η, ∀ s ∈ (univ : Set ℝ), ‖fderiv ℝ ψ (s • x) x‖ ≤ |K| := by
    filter_upwards [ae_restrict_mem (hA.inter Metric.isClosed_closedBall.measurableSet)] with x hx s _
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.2
    calc
      _ ≤ ‖fderiv ℝ ψ (s • x)‖*‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ (s • x)‖*1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ |K| := by simpa only [mul_one] using (hK (s • x)).trans (le_abs_self K)
  have hd (x : Cover) (s : ℝ) : HasDerivAt (fun u : ℝ ↦ ψ (u • x)) (fderiv ℝ ψ (s • x) x) s := by
    convert! ((hψ.differentiable (by simp) (s • x)).hasFDerivAt).comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_smul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (univ_mem : univ ∈ 𝓝 t)
    (Eventually.of_forall hm) hi hm' hb (integrable_const (|K|))
    (ae_of_all _ fun x s _ ↦ hd x s)).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma dilation_tsupport_subset {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    tsupport (fun x : Cover ↦ ψ (t • x)) ⊆ Metric.ball (0 : Cover) 1 := by
  have hc : Continuous (fun x : Cover ↦ t • x) := by fun_prop
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ hc hx)
  have htx : t*‖x‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one ht)] using hh
  have hnx := mul_le_mul_of_nonneg_right ht (norm_nonneg x)
  simpa only [Metric.mem_ball,dist_zero_right] using (by nlinarith : ‖x‖ < 1)

lemma fderiv_dilation_apply {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ) (t : ℝ) (x : Cover) :
    fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x = t*fderiv ℝ ψ (t • x) x := by
  have hd := ((hψ (t • x)).hasFDerivAt).comp x ((hasFDerivAt_id x).const_smul t)
  have he := hd.fderiv
  change fderiv ℝ (ψ ∘ fun y : Cover ↦ t • id y) x = _ at he
  rw [show (fun y : Cover ↦ ψ (t • y)) = (ψ ∘ fun y : Cover ↦ t • id y) from rfl, he]
  simp

lemma dilation_radial_euler {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) +
      t*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (t • x) x) = 0 := by
  let η : Measure Cover := volume.restrict (A ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (t • x)) :=
    hψ.comp (contDiff_id.const_smul t)
  have hcs := dilation_tsupport_subset hs ht
  have hψs : HasCompactSupport ψ := (isCompact_closedBall (0 : Cover) 1).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  have hi : Integrable (fun x : Cover ↦ ψ (t • x)) η := by
    obtain ⟨M,hM⟩ := hψs.exists_bound_of_continuous hψ.continuous
    exact Integrable.of_bound hcomp.continuous.aestronglyMeasurable M (ae_of_all _ fun x ↦ hM _)
  have hdi : Integrable (fun x : Cover ↦ fderiv ℝ ψ (t • x) x) η := by
    obtain ⟨K,hK⟩ := (hψs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
    have hd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
    have hc : Continuous (fun x : Cover ↦ fderiv ℝ ψ (t • x) x) :=
      (hd.comp (by fun_prop : Continuous (fun x : Cover ↦ t • x))).clm_apply continuous_id
    apply Integrable.of_bound hc.aestronglyMeasurable |K|
    filter_upwards [ae_restrict_mem (hA.inter Metric.isClosed_closedBall.measurableSet)] with x hx
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.2
    calc
      _ ≤ ‖fderiv ℝ ψ (t • x)‖*‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ (t • x)‖*1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ |K| := by simpa only [mul_one] using (hK (t • x)).trans (le_abs_self K)
  have he := hrad _ hcomp hcs
  have hz (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) 1) :
      3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x = 0 := by
    have hn : x ∉ tsupport (fun y : Cover ↦ ψ (t • y)) :=
      fun hh ↦ hx (Metric.ball_subset_closedBall (hcs hh))
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn]
    simp
  have heq : (∫ x in A, 3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1,
        3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x := by
    rw [inter_comm A, ← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hz
  rw [heq] at he
  simp_rw [fderiv_dilation_apply (hψ.differentiable (by simp))] at he
  rw [integral_add (hi.const_mul 3) (hdi.const_mul t),integral_const_mul,integral_const_mul] at he
  exact he

theorem radial_flux_dilation_pairing {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    t^3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ x := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall (0 : Cover) 1).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun s ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (s • x)
  let J : ℝ → ℝ := fun s ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (s • x) x
  have hd (s : ℝ) (hs' : s ∈ Ici (1 : ℝ)) : HasDerivAt (fun s ↦ s^3*I s) 0 s := by
    have heg : 3*I s+s*J s = 0 := dilation_radial_euler hA hrad hψ hs hs'
    have hdiff : HasDerivAt I (J s) s := hasDerivAt_setIntegral_dilation hA hψ hψs s
    convert! (((hasDerivAt_id s).pow 3).mul hdiff).congr_deriv (show
      (3*(s^(3-1))*1)*I s+s^3*J s = 0 from by
        calc
          _ = s^2*(3*I s+s*J s) := by ring
          _ = 0 := by rw [heg,mul_zero]) using 1
    all_goals try with_reducible_and_instances rfl
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs' ↦ (hd s hs').hasDerivWithinAt) (fun _ _ ↦ by simp : ∀ x ∈ Ici (1 : ℝ), ‖(0 : ℝ)‖ ≤ 0)
    (convex_Ici (1 : ℝ)) (show (1 : ℝ) ∈ Ici (1 : ℝ) by simp) (show t ∈ Ici (1 : ℝ) from ht)
  have he : t^3*I t = (1 : ℝ)^3*I 1 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))
  simpa only [I,one_pow,one_mul,one_smul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_indicator_dilation_local {A : Set Cover} (hA : MeasurableSet A)
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    {t : ℝ} (ht : 1 ≤ t) :
    (∫ x, ψ (t • x)*A.indicator (fun _ ↦ (1 : ℝ)) x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x) := by
  have hs' := dilation_tsupport_subset hs ht
  have hind : (fun x : Cover ↦ ψ (t • x)*A.indicator (fun _ ↦ (1 : ℝ)) x) =
      A.indicator (fun x ↦ ψ (t • x)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hind,integral_indicator hA]
  rw [inter_comm A,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun y : Cover ↦ ψ (t • y))
    (fun hh ↦ hx (Metric.ball_subset_closedBall (hs' hh)))

lemma radial_flux_cone_test {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    (∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) =
      ∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) x := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have he := integral_cover_affine_scaling
    (fun x : Cover ↦ ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) 0 ht0
  simp only [add_zero,smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at he
  rw [he,integral_indicator_dilation_local hA hs ht]
  have hh := radial_flux_dilation_pairing hA hrad hψ hs ht
  rw [hh]
  have he1 := integral_indicator_dilation_local hA hs (t := 1) le_rfl
  simpa only [one_smul] using he1.symm

theorem radial_flux_cone_ae {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {t : ℝ} (ht : 1 ≤ t) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A) := by
  let f : Cover → ℝ := A.indicator (fun _ ↦ 1)
  have hm : Measurable f := measurable_const.indicator hA
  have hm' : Measurable (fun x : Cover ↦ f (t⁻¹ • x)) := hm.comp (by fun_prop)
  have hb (x : Cover) : ‖f x‖ ≤ 1 := cover_indicator_bound A x
  have hli : LocallyIntegrable f (volume : Measure Cover) :=
    (memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).locallyIntegrable le_top
  have hli' : LocallyIntegrable (fun x : Cover ↦ f (t⁻¹ • x)) (volume : Measure Cover) :=
    (memLp_top_of_bound hm'.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ hb _)).locallyIntegrable le_top
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hli'.sub hli).locallyIntegrableOn (Metric.ball (0 : Cover) 1)) (fun ψ hψ hψs hs ↦ ?_)
  · filter_upwards [hz] with x hx hxin
    have he : f (t⁻¹ • x) = f x := sub_eq_zero.mp (hx hxin)
    by_cases h1 : t⁻¹ • x ∈ A <;> by_cases h2 : x ∈ A <;> simp [f,h1,h2] at he ⊢
  · have hi : Integrable ψ (volume : Measure Cover) := hψ.continuous.integrable_of_hasCompactSupport hψs
    have hi1 : Integrable (fun x : Cover ↦ ψ x*f (t⁻¹ • x)) :=
      hi.mul_bdd hm'.aestronglyMeasurable (ae_of_all _ fun x ↦ hb _)
    have hi2 : Integrable (fun x : Cover ↦ ψ x*f x) :=
      hi.mul_bdd hm.aestronglyMeasurable (ae_of_all _ hb)
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub,integral_sub hi1 hi2]
    exact sub_eq_zero.mpr (radial_flux_cone_test hA hrad hψ hs ht)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSecondaryPlanarData
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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma blowup_normal_closedBall_mass {ν : FiniteMeasure BlowupNormalBundle} {θ R : ℝ}
    (hm : ∀ s : ℝ, 0 < s → s < R →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) s} = θ*s^2)
    {b : ℝ} (hb : 0 < b) (hbR : b < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.closedBall (0 : Cover) b} = θ*b^2 := by
  apply le_antisymm
  · have ht : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[>] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbR)] with s hbs hsR
    rw [← hm s (hb.trans hbs) hsR]
    exact measureReal_mono (fun _ hz ↦ Metric.closedBall_subset_ball hbs hz)
  · rw [← hm b hb hbR]
    exact measureReal_mono (fun _ hz ↦ Metric.ball_subset_closedBall hz)

theorem isMinimizerAt_blowup_perimeter_eq {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hm : ∀ s : ℝ, 0 < s → s < 2 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) s} = θ*s^2)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2) := by
  have hb2 : b < 2 := by linarith
  have hp : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal (θ*b^2) := by
    have hh := coverLocalPerimeter_le_normal Metric.isClosed_closedBall.measurableSet
      (Metric.closedBall_subset_closedBall hb1) hflux
    have he := blowup_normal_closedBall_mass hm hb hb2
    rw [← he,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact hh
  have hfin : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp
  let L := (coverLocalPerimeter A (Metric.closedBall (0 : Cover) b)).toReal
  have hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hfin).ge
  have hlow : θ*b^2 ≤ L := by
    have ht : Tendsto (fun a : ℝ ↦ θ*a^2) (𝓝[<] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with a hab ha
    exact isMinimizerAt_blowup_competitor_bound hV hE hmin hμ hθ r hr hrlim hA hA hconv ha hab hb2.le
      ENNReal.toReal_nonneg hL (by simp)
  apply (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (mul_nonneg hθ0 (sq_nonneg b))]
  exact le_antisymm
    ((ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg hθ0 (sq_nonneg b))).mp hp) hlow

theorem isMinimizerAt_blowup_local_minimal {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b ≤ R)
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2))
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) := by
  by_cases hfin : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) = ⊤
  · rw [hfin]
    exact le_top
  let L := (coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)).toReal
  have hL : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hfin).ge
  have hlow : θ*b^2 ≤ L := by
    have ht : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[<] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)] with s hsb has
    exact isMinimizerAt_blowup_competitor_bound hV hE hmin hμ hθ r hr hrlim hA hB hconv
      (ha.trans has) hsb hbR ENNReal.toReal_nonneg hL
      (hAB.trans (Metric.ball_subset_ball has.le))
  rw [heq]
  exact (ENNReal.ofReal_le_ofReal hlow).trans_eq (ENNReal.ofReal_toReal hfin)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalCoverMap
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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_strict_C1_cone_blowup_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ),
      MeasurableSet A ∧ 0 < θ ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      (∀ b : ℝ, 0 < b → b < 2 →
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) b} = θ*b^2) ∧
      (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
        ⟪(z.2 : Cover),z.1⟫ = 0) ∧
      (∀ p : Cover, ‖p‖ < 1 → p ≠ 0 → p ∈ coverEssentialBoundary A → CoverC1BoundaryAt A p) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) := by
  have hc := cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ) < 1/2)
  obtain ⟨θ',hθ'0,hdens⟩ := exists_density_of_cmc_monotone (by norm_num : (0 : ℝ) < 1/4)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH cubeCenter hc)
  obtain ⟨A,ν,θ,φ,U,hA,hθ0,hφ,hU,hconv,hν,hm,hflux,hrad⟩ :=
    isMinimizerAt_paired_blowup hV hE hmin hμ hH cubeCenter
      (by norm_num : (0 : ℝ) < 1/4) hc r hr hrlim
  have hrl : Tendsto (fun i ↦ r (φ i)) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have heθ : θ'=θ := by
    have hh := blowup_limit_ball_mass cubeCenter (fun i ↦ r (φ i)) (fun i ↦ hr _)
      (hrl.mono_left hU) hdens hν (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    have hh' := hm 1 (by norm_num) (by norm_num)
    norm_num at hh hh'
    exact hh.symm.trans hh'
  subst θ'
  have hsp : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ) := by
    apply hdens.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with t ht
    change cellBallMass μ cubeCenter t / t^2 = _
    rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter t
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ht.le)).trans hc)]
  have heq (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) := isMinimizerAt_blowup_perimeter_eq
    hV hE hmin hμ hθ0 hsp (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hm
    (fun F hF hs ↦ (hflux F hF hs).2) hb hb1
  have hcone (t : ℝ) (ht : 1 ≤ t) : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A) :=
    radial_flux_cone_ae hA (fun ψ hψ hs ↦
      limit_set_radial_flux (fun F hF hFs ↦ (hflux F hF hFs).2) hrad hψ hs) ht
  have hC1 (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0) (hbd : p ∈ coverEssentialBoundary A) :=
    actual_primary_offvertex_C1 hV hE hmin hcenter hμ hH (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hconv hcone hflux p hp hp0 hbd
  refine ⟨A,ν,θ,φ,hA,isMinimizerAt_density_pos hV hE hmin hμ hcenter hsp,hφ,hconv,heq,?_,hcone,hm,hrad,hC1,hflux⟩
  · intro B hB a b ha hab hb1 hAB
    exact isMinimizerAt_blowup_local_minimal hV hE hmin hμ hsp (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hB hconv ha hab (by linarith : b ≤ 2)
      (heq b (ha.trans hab) hb1) hAB

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup_oai := @OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup_oai
