-- Prove2me | solution 1 for OAI.CubicTorus.SmallStandardRegion.bv_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:49:34.334989+00:00
-- url     : https://prove2.me/submissions/baebc314-a1b8-48a7-bd3e-65faa3c8335f

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001

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

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

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

lemma torus_coordinate_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus => x i) torusVolume volume := by
  exact (measurePreserving_eval (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ)))) i).comp
    torus_to_product_measurePreserving

lemma measurableSet_canonicalSlab (V : ℝ) : MeasurableSet (canonicalSlab V) := by
  exact measurableSet_lt (by fun_prop) measurable_const

lemma volume_canonicalSlab {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (canonicalSlab V) = ENNReal.ofReal V := by
  have heq : canonicalSlab V = (fun x : Torus => x 0) ⁻¹' Metric.ball 0 (V / 2) := by
    ext x
    simp [canonicalSlab, Metric.mem_ball, dist_zero_right]
  rw [heq, (torus_coordinate_measurePreserving 0).measure_preimage measurableSet_ball.nullMeasurableSet]
  rw [← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall]
  congr 1
  rw [min_eq_right (by linarith [hV.2] : 2 * (V / 2) ≤ 1)]
  ring

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
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

end CubicTorus

namespace CubicTorus

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

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

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

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

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

lemma shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    shortestLift (x - y) = shortestLift (x - c) - shortestLift (y - c) := by
  apply shortestLift_eq_of_lift
  · simp only [quotientMap_sub, quotientMap_shortestLift]; abel
  · exact (norm_sub_le _ _).trans_lt (by
      simpa only [norm_shortestLift, ← dist_eq_norm] using hxy)

lemma dist_shortestLift_sub_local {c x y : Torus} (hxy : dist x c + dist y c < 1 / 2) :
    dist (shortestLift (x - c)) (shortestLift (y - c)) = dist x y := by
  rw [dist_eq_norm, ← shortestLift_sub_local hxy, norm_shortestLift, ← dist_eq_norm]

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

lemma radialDensityField_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityField a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityField_tsupport hr hε)

lemma divergence_sub_const (a x : Cover) : divergence (fun y : Cover ↦ y - a) x = 3 := by
  rw [divergence, fderiv_sub_const a]
  simp [EuclideanSpace.single]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupComplement
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

lemma divergence_eq_trace (F : Cover → Cover) (x : Cover) :
    divergence F x = LinearMap.trace ℝ Cover (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [divergence,Matrix.trace,LinearMap.toMatrix_apply]

lemma divergence_isometry_pullback (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : Differentiable ℝ F) (x : Cover) :
    divergence (fun y ↦ R.symm (F (R y))) x = divergence F (R x) := by
  rw [divergence_eq_trace,divergence_eq_trace]
  have hd := R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hF (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ R.symm (F (R y))) _ x at hd
  rw [hd.fderiv]
  have he : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap =
      R.symm.toLinearEquiv.conj (fderiv ℝ F (R x)).toLinearMap := rfl
  rw [he,LinearMap.trace_conj']

lemma isometry_pullback_contDiff (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ R.symm (F (R x))) :=
  R.symm.toContinuousLinearEquiv.contDiff.comp (hF.comp R.toContinuousLinearEquiv.contDiff)

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

end CubicTorus.UpperComparison

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

lemma divergence_inner_radialDensityField {a x : Cover} {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (hx : x ∈ Metric.ball a r) :
    divergence (radialDensityField a s (s^2-r^2)) x = 3 := by
  have he : radialDensityField a s (s^2-r^2) =ᶠ[𝓝 x] (fun y : Cover ↦ y-a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [radialDensityField,radialDensityWeight_one_on_inner hr.le hrs (Metric.ball_subset_closedBall hy),one_smul]
  simp only [divergence,he.fderiv_eq]
  exact divergence_sub_const a x

lemma ballCalibration_contDiff (r s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ballCalibration r s) :=
  (radialDensityField_contDiff _ _ _).const_smul _

lemma ballCalibration_compact {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    HasCompactSupport (ballCalibration r s) := by
  have hs0 : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  change HasCompactSupport ((fun _ : Cover ↦ s⁻¹) • radialDensityField cubeCenter s (s^2-r^2))
  exact (radialDensityField_hasCompactSupport (a := cubeCenter) hs0 hε).smul_left

lemma ballCalibration_support {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    tsupport (ballCalibration r s) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  have hs0 : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  exact (tsupport_smul_subset_right (fun _ : Cover ↦ s⁻¹)
    (radialDensityField cubeCenter s (s^2-r^2))).trans
    ((radialDensityField_tsupport hs0 hε).trans (cubeCenter_closedBall_interior hs))

lemma ballCalibration_norm {r s : ℝ} (hr : 0 < r) (hrs : r < s) (x : Cover) :
    ‖ballCalibration r s x‖ ≤ 1 := by
  have hs0 : 0 < s := hr.trans hrs
  have hε : 0 < s^2-r^2 := by nlinarith
  rw [ballCalibration,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0)]
  exact (mul_le_mul_of_nonneg_left (radialDensityField_norm_le hs0.le hε x)
    (inv_nonneg.mpr hs0.le)).trans_eq (inv_mul_cancel₀ hs0.ne')

lemma ballCalibration_divergence {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2)
    (x : Cover) (hx : x ∈ Metric.ball cubeCenter r) :
    divergence (latticePeriodize (ballCalibration r s)) x = 3/s := by
  have hm := coverBall_subset_cube (hrs.le.trans hs.le) hx
  have he := latticePeriodize_eventuallyEq (ballCalibration_compact hr hrs)
    (ballCalibration_support hr hrs hs) (fun i ↦ ⟨(hm i).1,(hm i).2.le⟩)
  change (∑ i : Fin 3, (fderiv ℝ (latticePeriodize (ballCalibration r s)) x
    (EuclideanSpace.single i 1)) i) = _
  rw [he.fderiv_eq]
  change divergence (fun y ↦ s⁻¹ • radialDensityField cubeCenter s (s^2-r^2) y) x = _
  rw [divergence_const_smul ((radialDensityField_contDiff _ _ _).differentiable (by simp) x) (s⁻¹),
    divergence_inner_radialDensityField hr hrs hx]
  ring

lemma integral_const_coverBall (r k : ℝ) (hr : 0 ≤ r) :
    (∫ _ in Metric.ball cubeCenter r, k ∂(volume : Measure Cover)) = k*(r^3*(Real.pi*4/3)) := by
  rw [integral_const]
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,
    EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

lemma ball_calibration_flux_le {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal (3/s * (r^3*(Real.pi*4/3))) ≤ perimeter (cubeBall r) := by
  have hp := admissible_latticePeriodize (ballCalibration_contDiff r s)
    (ballCalibration_compact hr hrs) (ballCalibration_support hr hrs hs) (ballCalibration_norm hr hrs)
  have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' cubeBall r,
      divergence (latticePeriodize (ballCalibration r s)) x) ≤ perimeter (cubeBall r) :=
    le_iSup_of_le _ (le_iSup_of_le hp le_rfl)
  rw [cubeBall_lift (hrs.le.trans hs.le)] at hh
  rwa [setIntegral_congr_fun Metric.isOpen_ball.measurableSet (ballCalibration_divergence hr hrs hs),
    integral_const_coverBall r (3/s) hr.le] at hh

theorem perimeter_cubeBall_eq {r : ℝ} (hr : 0 < r) (hs : r < 1/2) :
    perimeter (cubeBall r) = ENNReal.ofReal (4*Real.pi*r^2) := by
  apply le_antisymm
  · exact UpperComparison.perimeter_cubeBall_le hr hs.le
  · have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (3/s*(r^3*(Real.pi*4/3)))) (𝓝[>] r)
        (𝓝 (ENNReal.ofReal (4*Real.pi*r^2))) := by
      have hl : Tendsto (fun s : ℝ ↦ 3/s*(r^3*(Real.pi*4/3))) (𝓝 r)
          (𝓝 (3/r*(r^3*(Real.pi*4/3)))) :=
        ((continuousAt_const.div continuousAt_id hr.ne').mul continuousAt_const).tendsto
      have hv : 3/r*(r^3*(Real.pi*4/3)) = 4*Real.pi*r^2 := by field_simp
      rw [hv] at hl
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hl.mono_left nhdsWithin_le_nhds)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with s hrs hs
    exact ball_calibration_flux_le hr hrs hs

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

lemma metricBall_eq_translate (c : Torus) (r : ℝ) :
    Metric.ball c r=(fun x : Torus ↦ x+(-c)) ⁻¹' Metric.ball 0 r := by
  ext x
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,sub_zero,← sub_eq_add_neg]

lemma metricBall_perimeter (c : Torus) {r : ℝ} (hr0 : 0 < r) (hr : r<1/2) :
    perimeter (Metric.ball c r)=ENNReal.ofReal (4*Real.pi*r^2) := by
  rw [metricBall_eq_translate,perimeter_translation Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    UpperComparison.centeredBall_eq_cubeBall_preimage,
    perimeter_translation (UpperComparison.measurableSet_cubeBall r).nullMeasurableSet]
  exact perimeter_cubeBall_eq hr0 hr

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

lemma lattice (e : LatticeIsometry) (m : Fin 3 → ℤ) :
    ∃ n : Fin 3 → ℤ,e.cover (latticeVector m)=latticeVector n := by
  have he : quotientMap (e.cover (latticeVector m))=quotientMap (0 : Cover) := by
    rw [e.commute,quotientMap_latticeVector,e.map_zero]
    ext j; simp [quotientMap]
  obtain ⟨n,hn⟩ := same_quotient_lattice he
  exact ⟨n,by simpa only [zero_add] using hn⟩

lemma pullback_contDiff (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (e.pullback F) :=
  isometry_pullback_contDiff e.cover hF

lemma pullback_periodic (e : LatticeIsometry) {F : Cover → Cover}
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∀ m x,e.pullback F (x+latticeVector m)=e.pullback F x := by
  intro m x
  obtain ⟨n,hn⟩ := e.lattice m
  simp only [pullback,LinearIsometryEquiv.map_add,hn,hp]

lemma pullback_admissible (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (e.pullback F) := by
  refine ⟨e.pullback_contDiff hF.1,e.pullback_periodic hF.2.1,fun x ↦ ?_⟩
  simpa only [pullback,LinearIsometryEquiv.norm_map] using hF.2.2 (e.cover x)

lemma divergence_pullback (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (e.pullback F) x=divergence F (e.cover x) :=
  divergence_isometry_pullback e.cover (hF.differentiable (by simp)) x

lemma flux (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (e.torus ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence (e.symm.pullback F) x := by
  have hG := e.symm.pullback_admissible hF
  rw [←setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1)
    (hE.preimage e.torus.continuous.measurable),
    ←setIntegral_lift (continuous_divergence hG.1) (divergence_periodic hG.2.1) hE]
  have he : (fun z : Torus ↦ divergence F (representative z))=
      fun z ↦ divergence (e.symm.pullback F) (representative (e.torus z)) := by
    funext z
    rw [e.symm.divergence_pullback hF.1]
    have hq : quotientMap (e.cover.symm (representative (e.torus z)))=quotientMap (representative z) := by
      change quotientMap (e.symm.cover (representative (e.torus z)))=quotientMap (representative z)
      rw [e.symm.commute,quotientMap_representative,quotientMap_representative]
      exact e.torus.symm_apply_apply z
    obtain ⟨n,hn⟩ := same_quotient_lattice hq
    change divergence F (representative z)=divergence F (e.cover.symm (representative (e.torus z)))
    rw [hn,divergence_periodic hF.2.1]
  rw [he]
  exact e.measurePreserving.setIntegral_preimage_emb e.torus.toHomeomorph.measurableEmbedding
    (fun z ↦ divergence (e.symm.pullback F) (representative z)) E

lemma perimeter_measurable (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have hle (a : LatticeIsometry) {A : Set Torus} (hA : MeasurableSet A) :
      perimeter (a.torus ⁻¹' A)≤perimeter A := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    rw [a.flux hF hA]
    exact le_iSup₂_of_le (a.symm.pullback F) (a.symm.pullback_admissible hF) le_rfl
  apply le_antisymm (hle e hE)
  have hh := hle e.symm (hE.preimage e.torus.continuous.measurable)
  have hset : e.symm.torus ⁻¹' (e.torus ⁻¹' E)=E := by
    ext x
    change e.torus (e.torus.symm x)∈E ↔ x∈E
    rw [e.torus.apply_symm_apply]
  rwa [hset] at hh

theorem perimeter_eq (e : LatticeIsometry) {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [←perimeter_congr_ae hp,←perimeter_congr_ae he]
  exact e.perimeter_measurable (measurableSet_toMeasurable _ _)

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma norm_quotientMap_of_small {x : Cover} (hx : ‖x‖ < 1/2) :
    ‖quotientMap x‖ = ‖x‖ := by
  rw [←norm_shortestLift,shortestLift_quotientMap hx]

lemma centeredIsometryLift_norm (φ : Torus ≃ᵢ Torus) {x : Cover} (hx : ‖x‖ < 1/2) :
    ‖centeredIsometryLift φ x‖ = ‖x‖ := by
  rw [centeredIsometryLift,norm_shortestLift,←dist_eq_norm,φ.dist_eq,
    dist_zero_right,norm_quotientMap_of_small hx]

lemma centeredIsometryLift_dist (φ : Torus ≃ᵢ Torus) {x y : Cover}
    (hx : ‖x‖ < 1/4) (hy : ‖y‖ < 1/4) :
    dist (centeredIsometryLift φ x) (centeredIsometryLift φ y) = dist x y := by
  have hh : dist (φ (quotientMap x)) (φ 0) + dist (φ (quotientMap y)) (φ 0) < 1/2 := by
    rw [φ.dist_eq,φ.dist_eq,dist_zero_right,dist_zero_right]
    exact lt_of_le_of_lt (add_le_add (norm_quotientMap_le _) (norm_quotientMap_le _)) (by linarith)
  rw [centeredIsometryLift,centeredIsometryLift,dist_shortestLift_sub_local hh,
    φ.dist_eq,dist_eq_norm,←quotientMap_sub,norm_quotientMap_of_small,
    ←dist_eq_norm]
  exact (norm_sub_le _ _).trans_lt (by linarith)

lemma centeredIsometryLift_inner (φ : Torus ≃ᵢ Torus) {x y : Cover}
    (hx : ‖x‖ < 1/4) (hy : ‖y‖ < 1/4) :
    ⟪centeredIsometryLift φ x,centeredIsometryLift φ y⟫ = ⟪x,y⟫ := by
  have hd := centeredIsometryLift_dist φ hx hy
  rw [dist_eq_norm,dist_eq_norm] at hd
  have hn := norm_sub_sq_real (centeredIsometryLift φ x) (centeredIsometryLift φ y)
  rw [centeredIsometryLift_norm φ (by linarith),
    centeredIsometryLift_norm φ (by linarith),hd,norm_sub_sq_real] at hn
  linarith

theorem torusIsometry_local_linear (φ : Torus ≃ᵢ Torus) :
    ∃ L : Cover ≃ₗᵢ[ℝ] Cover, ∀ x, ‖x‖ < 1/4 → centeredIsometryLift φ x = L x := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let v : Fin 3 → Cover := fun i ↦ (8 : ℝ) • centeredIsometryLift φ ((1/8 : ℝ) • b i)
  have hb (i : Fin 3) : ‖(1/8 : ℝ) • b i‖ < 1/4 := by
    rw [norm_smul,b.norm_eq_one,Real.norm_eq_abs]
    norm_num
  have ho : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp only [v]
    rw [real_inner_smul_left,real_inner_smul_right,
      centeredIsometryLift_inner φ (hb i) (hb j),
      real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
    split_ifs <;> norm_num
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    rw [ho.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [Cover])]
  let B : OrthonormalBasis (Fin 3) ℝ Cover := OrthonormalBasis.mk ho hspan
  let L : Cover ≃ₗᵢ[ℝ] Cover := b.equiv B (Equiv.refl _)
  refine ⟨L,fun x hx ↦ ?_⟩
  apply B.repr.injective
  ext i
  simp only [OrthonormalBasis.repr_apply_apply]
  have hBi : B i = v i := by simp [B]
  have hLi : L (b i) = B i := by simp [L]
  nth_rw 2 [←hLi]
  rw [L.inner_map_map,hBi]
  dsimp only [v]
  rw [real_inner_smul_left,centeredIsometryLift_inner φ (hb i) hx,
    real_inner_smul_left]
  ring

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Rigidity_TwoVolumeNodal
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

lemma quotientMap_nsmul (n : ℕ) (v : Cover) : quotientMap (n • v) = n • quotientMap v := by
  induction n with
  | zero => ext i; simp [quotientMap]
  | succ n ih => simp only [succ_nsmul,quotientMap_add,ih]

lemma torus_same_short_step {a b c : Torus} {δ : ℝ}
    (hsmall : δ < 1/4) (hab : dist a b = δ) (hbc : dist c b = δ)
    (hac : dist c a = 2*δ) : c-b = b-a := by
  let u := shortestLift (c-b)
  let v := -shortestLift (a-b)
  have hu : ‖u‖ = δ := by simpa only [u,norm_shortestLift,←dist_eq_norm] using hbc
  have hv : ‖v‖ = δ := by simpa only [v,norm_neg,norm_shortestLift,←dist_eq_norm] using hab
  have hs : ‖u+v‖ = 2*δ := by
    change ‖shortestLift (c-b)-shortestLift (a-b)‖ = 2*δ
    rw [←shortestLift_sub_local (by rw [hab,hbc]; linarith),
      norm_shortestLift,←dist_eq_norm,hac]
  have he : u=v := eq_of_norm_eq_of_norm_add_eq (hu.trans hv.symm)
    (by rw [hs,hu,hv]; ring)
  have hh := congrArg quotientMap he
  simpa only [u,v,quotientMap_neg,quotientMap_shortestLift,neg_sub] using hh

lemma isometry_straight_step (φ : Torus ≃ᵢ Torus) (x v : Cover) (hv : ‖v‖ < 1/4) :
    φ (quotientMap (x+v+v))-φ (quotientMap (x+v)) =
      φ (quotientMap (x+v))-φ (quotientMap x) := by
  apply torus_same_short_step hv
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x-(x+v) = -v := by abel
    rw [he,quotientMap_neg,norm_neg,norm_quotientMap_of_small (by linarith)]
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x+v+v-(x+v) = v := by abel
    rw [he,norm_quotientMap_of_small (by linarith)]
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x+v+v-x = (2 : ℝ) • v := by module
    rw [he,norm_quotientMap_of_small]
    · simp [norm_smul]
    · rw [norm_smul]; norm_num; linarith

lemma isometry_straight_nsmul (φ : Torus ≃ᵢ Torus) (v : Cover) (hv : ‖v‖ < 1/4) (n : ℕ) :
    φ (quotientMap (n • v)) = n • (φ (quotientMap v)-φ 0)+φ 0 := by
  have hq0 : quotientMap (0 : Cover) = 0 := by ext i; simp [quotientMap]
  have hd : ∀ k : ℕ,φ (quotientMap ((k+1) • v))-φ (quotientMap (k • v)) =
      φ (quotientMap v)-φ 0 := by
    intro k
    induction k with
    | zero => simp [hq0]
    | succ k ih =>
      have hs := isometry_straight_step φ (k • v) v hv
      simpa only [succ_nsmul,add_nsmul,one_nsmul,Nat.succ_eq_add_one] using hs.trans ih
  induction n with
  | zero => simp [hq0]
  | succ n ih =>
    have hh := hd n
    rw [ih] at hh
    have he := sub_eq_iff_eq_add.mp hh
    change φ (quotientMap ((n+1) • v)) = (n+1) • (φ (quotientMap v)-φ 0)+φ 0
    rw [he,add_nsmul,one_nsmul]
    abel

theorem torusIsometry_global_linear (φ : Torus ≃ᵢ Torus) :
    ∃ L : Cover ≃ₗᵢ[ℝ] Cover, ∀ x, φ (quotientMap x) = quotientMap (L x)+φ 0 := by
  obtain ⟨L,hL⟩ := torusIsometry_local_linear φ
  refine ⟨L,fun x ↦ ?_⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (4*‖x‖+1)
  have hnpos : (0 : ℝ) < n := by linarith [norm_nonneg x]
  let v := (n : ℝ)⁻¹ • x
  have hv : ‖v‖ < 1/4 := by
    dsimp only [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnpos)]
    rw [←div_eq_inv_mul,div_lt_iff₀ hnpos]
    linarith
  have hnV : n • v = x := by
    rw [←Nat.cast_smul_eq_nsmul ℝ]
    dsimp only [v]
    rw [smul_smul,mul_inv_cancel₀ hnpos.ne',one_smul]
  have hg : φ (quotientMap v)-φ 0 = quotientMap (L v) := by
    simpa only [centeredIsometryLift,quotientMap_shortestLift] using congrArg quotientMap (hL v hv)
  have hh := isometry_straight_nsmul φ v hv n
  rw [hnV,hg] at hh
  simpa only [←quotientMap_nsmul,←map_nsmul L,hnV] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem torusIsometry_lattice_translation (φ : Torus ≃ᵢ Torus) :
    ∃ e : LatticeIsometry, ∀ z,φ z=e.torus z+φ 0 := by
  obtain ⟨L,hL⟩ := torusIsometry_global_linear φ
  let ψ : Torus ≃ᵢ Torus :=
    { toFun := fun z ↦ φ z-φ 0
      invFun := fun z ↦ φ.symm (z+φ 0)
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      isometry_toFun := isometry_iff_dist_eq.mpr (by intro x y; simpa only [dist_sub_right] using φ.dist_eq x y) }
  let e : LatticeIsometry :=
    { cover := L
      torus := ψ
      commute := fun x ↦ by change quotientMap (L x)=φ (quotientMap x)-φ 0; rw [hL]; abel }
  refine ⟨e,fun z ↦ ?_⟩
  change φ z=(φ z-φ 0)+φ 0
  abel

theorem torusIsometry_measurePreserving (φ : Torus ≃ᵢ Torus) :
    MeasurePreserving φ torusVolume torusVolume := by
  obtain ⟨e,he⟩ := torusIsometry_lattice_translation φ
  have hf : (fun z : Torus ↦ z+φ 0) ∘ e.torus = φ := by
    funext z
    exact (he z).symm
  rw [←hf]
  exact (measurePreserving_add_right torusVolume (φ 0)).comp e.measurePreserving

theorem perimeter_torusIsometry (φ : Torus ≃ᵢ Torus) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) : perimeter (φ ⁻¹' E)=perimeter E := by
  obtain ⟨e,he⟩ := torusIsometry_lattice_translation φ
  have hs : φ ⁻¹' E = e.torus ⁻¹' ((fun z ↦ z+φ 0) ⁻¹' E) := by
    ext z
    change φ z∈E ↔ e.torus z+φ 0∈E
    rw [he z]
  rw [hs,e.perimeter_eq,
    perimeter_translation hE]
  exact hE.preimage (measurePreserving_add_right torusVolume (φ 0)).quasiMeasurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isometry_image_eq_symm_preimage (φ : Torus ≃ᵢ Torus) (F : Set Torus) :
    φ '' F = φ.symm ⁻¹' F := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨φ.symm x,hx,φ.apply_symm_apply x⟩

lemma CongruentAE.nullMeasurableSet {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : NullMeasurableSet E torusVolume := by
  obtain ⟨φ,hφ⟩ := h
  rw [isometry_image_eq_symm_preimage] at hφ
  exact (hF.preimage (torusIsometry_measurePreserving φ.symm).quasiMeasurePreserving).congr hφ.symm

theorem CongruentAE.perimeter_eq {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : perimeter E=perimeter F := by
  obtain ⟨φ,hφ⟩ := h
  rw [perimeter_congr_ae hφ,isometry_image_eq_symm_preimage,perimeter_torusIsometry φ.symm hF]

theorem CongruentAE.volume_eq {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : torusVolume E=torusVolume F := by
  obtain ⟨φ,hφ⟩ := h
  rw [measure_congr hφ,isometry_image_eq_symm_preimage,
    (torusIsometry_measurePreserving φ.symm).measure_preimage hF]

theorem stripe_congruentAE_slab {V : ℝ} (hV : V∈Icc 0 1) :
    CongruentAE (stripe V) (canonicalSlab V) := by
  let K : Set (AddCircle (1 : ℝ)) := {x | ((AddCircle.equivIco (1 : ℝ) 0) x : ℝ)<V}
  have hK : MeasurableSet K := measurableSet_lt
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable) measurable_const
  have he : ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc 0 1 : Set ℝ)
      =ᵐ[volume] Ioo 0 V := by
    filter_upwards [(volume : Measure ℝ).ae_ne (1 : ℝ)] with t ht
    apply propext
    constructor
    · rintro ⟨hK,hI⟩
      have hlt : t<1 := lt_of_le_of_ne hI.2 ht
      have hrep := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := 0)
        (show t∈Ico 0 (0+1) by exact ⟨hI.1.le,by simpa using hlt⟩)
      change ((AddCircle.equivIco (1 : ℝ) 0) (t : AddCircle (1 : ℝ)) : ℝ)<V at hK
      rw [hrep] at hK
      exact ⟨hI.1,hK⟩
    · intro hI
      have hlt : t<1 := lt_of_lt_of_le hI.2 hV.2
      refine ⟨?_,hI.1,hlt.le⟩
      change ((AddCircle.equivIco (1 : ℝ) 0) (t : AddCircle (1 : ℝ)) : ℝ)<V
      rw [AddCircle.equivIco_coe_of_mem (show t∈Ico 0 (0+1) by exact ⟨hI.1.le,by simpa using hlt⟩)]
      exact hI.2
  have hh := circle_interval_ae_ball hK (show (0 : ℝ)≤0 by rfl) hV.1 (by simpa using hV.2) (by simpa only [zero_add] using he)
  simp only [zero_add,sub_zero] at hh
  have ha := (torus_coordinate_measurePreserving 0).quasiMeasurePreserving.preimage_ae_eq hh
  obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V 0 (((V/2 : ℝ) : AddCircle (1 : ℝ)))
  refine ⟨φ,?_⟩
  rw [hφ]
  exact ha

lemma perimeter_canonicalSlab_le {V : ℝ} (hV : V∈Icc 0 1) :
    perimeter (canonicalSlab V)≤2 := by
  have hh := (stripe_congruentAE_slab hV).perimeter_eq (measurableSet_canonicalSlab V).nullMeasurableSet
  rw [←hh]
  exact perimeter_stripe_le hV

lemma finitePerimeter_canonicalSlab {V : ℝ} (hV : V∈Icc 0 1) :
    FinitePerimeter (canonicalSlab V) :=
  ⟨(measurableSet_canonicalSlab V).nullMeasurableSet,
    (perimeter_canonicalSlab_le hV).trans_lt (by norm_num)⟩

end CubicTorus

end
end

section

namespace CubicTorus.TwoVolume
noncomputable section
open Set Filter
open scoped Topology
open Reduction

lemma transitions : 0 < V₁ ∧ V₁ < V₂ ∧ V₂ < 1 / 2 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  dsimp [V₁, V₂]
  constructor
  · positivity
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith [sq_nonneg (4 - Real.pi)]
  · apply (div_lt_iff₀ hp).2
    linarith

lemma sphereArea_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ sphereArea v := by
  unfold sphereArea
  positivity

lemma sphereArea_cube {v : ℝ} (hv : 0 ≤ v) :
    sphereArea v ^ 3 = (9 * Real.pi / 2) * v ^ 2 := by
  have ha : ((9 * Real.pi / 2) ^ (1 / 3 : ℝ)) ^ 3 = 9 * Real.pi / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hb : (v ^ (2 / 3 : ℝ)) ^ 3 = v ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
    norm_num
  simp only [sphereArea, mul_pow, ha, hb]

lemma tubeArea_sq {v : ℝ} (hv : 0 ≤ v) : tubeArea v ^ 2 = Real.pi * v := by
  exact Real.sq_sqrt (mul_nonneg Real.pi_pos.le hv)

lemma sphereArea_le_tubeArea_iff {v : ℝ} (hv : 0 < v) :
    sphereArea v ≤ tubeArea v ↔ v ≤ V₁ := by
  have hs := sphereArea_cube hv.le
  have ht := tubeArea_sq hv.le
  have h0 : 0 < Real.pi ^ 2 * v ^ 3 := by positivity
  have h₆ : sphereArea v ^ 6 - tubeArea v ^ 6 =
      (81 / 4 * v - Real.pi) * (Real.pi ^ 2 * v ^ 3) := by
    calc
      _ = (sphereArea v ^ 3) ^ 2 - (tubeArea v ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs, ht]; ring
  have ht0 : 0 ≤ tubeArea v := Real.sqrt_nonneg _
  rw [← pow_le_pow_iff_left₀ (sphereArea_nonneg hv.le) ht0 (by decide : 6 ≠ 0)]
  rw [← sub_nonpos, h₆]
  dsimp [V₁]
  constructor
  · intro h
    by_contra! hn
    have hpos : 0 < 81 / 4 * v - Real.pi := by linarith
    exact (not_lt_of_ge h) (mul_pos hpos h0)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h0.le

lemma tubeArea_le_one_iff {v : ℝ} (_ : 0 ≤ v) : tubeArea v ≤ 1 ↔ v ≤ V₂ := by
  rw [tubeArea, Real.sqrt_le_iff]
  norm_num
  simpa [V₂, mul_comm] using (le_div_iff₀ Real.pi_pos : v ≤ 1 / Real.pi ↔ v * Real.pi ≤ 1).symm

lemma sphereArea_zero : sphereArea 0 = 0 := by norm_num [sphereArea]
lemma tubeArea_zero : tubeArea 0 = 0 := by simp [tubeArea]
lemma tubeArea_nonneg (v : ℝ) : 0 ≤ tubeArea v := Real.sqrt_nonneg _

lemma sphereArea_eq_tubeArea_V₁ : sphereArea V₁ = tubeArea V₁ := by
  have hs := sphereArea_cube transitions.1.le
  have ht := tubeArea_sq transitions.1.le
  have hp : sphereArea V₁ ^ 6 = tubeArea V₁ ^ 6 := by
    calc
      _ = (sphereArea V₁ ^ 3) ^ 2 := by ring
      _ = (tubeArea V₁ ^ 2) ^ 3 := by rw [hs, ht]; dsimp [V₁]; ring
      _ = _ := by ring
  exact (pow_left_inj₀ (sphereArea_nonneg transitions.1.le) (tubeArea_nonneg _)
    (by decide : (6 : ℕ) ≠ 0)).mp hp

lemma tubeArea_V₂ : tubeArea V₂ = 1 := by
  simp [tubeArea, V₂, ne_of_gt Real.pi_pos]

lemma envelope_sphere {v : ℝ} (hv : v ∈ Icc 0 V₁) : envelope v = sphereArea v := by
  have hvhalf : v ≤ 1 / 2 := hv.2.trans (transitions.2.1.le.trans transitions.2.2.le)
  have hmin : min v (1-v) = v := min_eq_left (by linarith)
  by_cases hz : v = 0
  · subst v; simp [envelope, sphereArea_zero, tubeArea_zero]
  have hpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hz)
  have hst := (sphereArea_le_tubeArea_iff hpos).2 hv.2
  have ht1 := (tubeArea_le_one_iff hv.1).2 (hv.2.trans transitions.2.1.le)
  simp only [envelope, hmin, min_eq_left ht1, min_eq_left hst]

lemma envelope_tube {v : ℝ} (hv : v ∈ Icc V₁ V₂) : envelope v = tubeArea v := by
  have hv0 : 0 < v := transitions.1.trans_le hv.1
  have hvhalf : v ≤ 1 / 2 := hv.2.trans transitions.2.2.le
  have hmin : min v (1-v) = v := min_eq_left (by linarith)
  have hts : tubeArea v ≤ sphereArea v := by
    by_cases heq : v = V₁
    · subst v; exact sphereArea_eq_tubeArea_V₁.ge
    · exact le_of_lt (not_le.1 (fun h => heq (le_antisymm
        ((sphereArea_le_tubeArea_iff hv0).1 h) hv.1)))
  have ht1 := (tubeArea_le_one_iff hv0.le).2 hv.2
  simp only [envelope, hmin, min_eq_left ht1, min_eq_right hts]

lemma envelope_constant {v : ℝ} (hv : v ∈ Icc V₂ (1-V₂)) : envelope v = 1 := by
  let w := min v (1-v)
  have hw : V₂ ≤ w := le_min hv.1 (by linarith [hv.2])
  have hw0 : 0 < w := (transitions.1.trans transitions.2.1).trans_le hw
  have ht1 : 1 ≤ tubeArea w := by
    by_cases heq : w = V₂
    · rw [heq, tubeArea_V₂]
    · exact le_of_lt (not_le.1 (fun h => heq
        (le_antisymm ((tubeArea_le_one_iff hw0.le).1 h) hw)))
  have hst : tubeArea w ≤ sphereArea w := by
    exact le_of_lt (not_le.1 (fun h =>
      (not_lt_of_ge ((sphereArea_le_tubeArea_iff hw0).1 h)) (transitions.2.1.trans_le hw)))
  change min (sphereArea w) (min (tubeArea w) 1) = 1
  rw [min_eq_right ht1, min_eq_right (ht1.trans hst)]

lemma candidateProfile_eq_two_envelope (v : ℝ) : candidateProfile v = 2 * envelope v := by
  have hc : (36 * Real.pi) ^ (1/3 : ℝ) = 2 * (9 * Real.pi / 2) ^ (1/3 : ℝ) := by
    have hcube (a : ℝ) (ha : 0 ≤ a) : (a ^ (1/3 : ℝ)) ^ 3 = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hcube _ (by positivity), mul_pow, hcube _ (by positivity)]
    ring
  simp only [candidateProfile, envelope, sphereArea, tubeArea, hc,
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

end
end CubicTorus.TwoVolume

end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma canonicalBall_radius_lt {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    (3*V/(4*Real.pi))^(1/3 : ℝ)<1/2 := by
  have hpos := hV.1
  have hc := UpperComparison.cube_cuberoot (3*V/(4*Real.pi)) (by positivity)
  apply (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp
  rw [hc]
  apply (div_lt_iff₀ (by positivity : 0<4*Real.pi)).mpr
  nlinarith [Real.pi_gt_three,hV.2]

lemma canonicalTube_radius_lt {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    Real.sqrt (V/Real.pi)<1/2 := by
  have hpos := hV.1
  apply (Real.sqrt_lt (by positivity) (by norm_num : (0 : ℝ)≤1/2)).mpr
  apply (div_lt_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three,hV.2]

theorem perimeter_canonicalBall_eq {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalBall V)=ENNReal.ofReal ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)) := by
  obtain ⟨hr0,_,_⟩ := UpperComparison.canonicalBall_radius_properties hV
  rw [canonicalBall,metricBall_perimeter 0 hr0 (canonicalBall_radius_lt hV),
    UpperComparison.ballArea_formula hV.1.le]

theorem perimeter_canonicalTube_eq {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V)=ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0,_,_⟩ := UpperComparison.canonicalTube_radius_properties hV
  change perimeter (UpperComparison.centeredTube _)=_
  rw [UpperComparison.centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (UpperComparison.measurableSet_cubeTube _).nullMeasurableSet,
    UpperComparison.perimeter_cubeTube_eq hr0 (canonicalTube_radius_lt hV),
    UpperComparison.tubeArea_formula hV.1.le]

theorem perimeter_canonicalSlab_eq {V : ℝ} (hV : V∈Ioo 0 1) :
    perimeter (canonicalSlab V)=2 := by
  let K : Set (AddCircle (1 : ℝ)) := Metric.ball 0 (V/2)
  have heq : (integerCharacter (Pi.single 0 (1 : ℤ))) ⁻¹' K=canonicalSlab V := by
    ext x
    simp [integerCharacter_single,K,Metric.mem_ball,dist_zero_right,canonicalSlab]
  have hm : (Pi.single 0 (1 : ℤ) : Fin 3 → ℤ)≠0 := by
    intro h
    have hh := congrFun h 0
    simp at hh
  have hvol : volume K=ENNReal.ofReal V := by
    rw [← volume_canonicalSlab ⟨hV.1.le,hV.2.le⟩,← heq]
    exact ((integerCharacter_measurePreserving hm).measure_preimage
      Metric.isOpen_ball.measurableSet.nullMeasurableSet).symm
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl Metric.isOpen_ball.measurableSet (measure_ne_top _ _),hvol]
    apply ne_of_gt
    apply tsub_pos_of_lt
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1)).mpr hV.2
  have hP := (finitePerimeter_canonicalSlab ⟨hV.1.le,hV.2.le⟩).2.ne
  have hh := circle_nontrivial_phase_lower_bound hm Metric.isOpen_ball.measurableSet
    (show volume K≠0 by rw [hvol]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hV.1)) hneg
    (show perimeter ((integerCharacter (Pi.single 0 (1 : ℤ))) ⁻¹' K)≠⊤ by rwa [heq])
  have hn : ‖latticeVector (Pi.single 0 (1 : ℤ))‖=1 := by
    have he : latticeVector (Pi.single 0 (1 : ℤ))=EuclideanSpace.single (0 : Fin 3) 1 := by
      ext i
      by_cases hi : i=0 <;> simp [latticeVector,Pi.single_apply,hi]
    rw [he,PiLp.norm_single]
    norm_num
  rw [hn,heq] at hh
  norm_num only [mul_one] at hh
  apply le_antisymm (perimeter_canonicalSlab_le ⟨hV.1.le,hV.2.le⟩)
  exact (ENNReal.toReal_le_toReal (by norm_num) hP).mp (by simpa using hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unit_sphereArea (V : ℝ) :
    (36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)=2*TwoVolume.sphereArea V := by
  have hc : (36*Real.pi)^(1/3 : ℝ)=2*(9*Real.pi/2)^(1/3 : ℝ) := by
    apply (show Odd (3 : ℕ) by decide).pow_injective
    dsimp only
    rw [mul_pow,UpperComparison.cube_cuberoot _ (by positivity),
      UpperComparison.cube_cuberoot _ (by positivity)]
    ring
  rw [hc,TwoVolume.sphereArea]
  ring

lemma candidateProfile_sphere {V : ℝ} (hV : V∈Icc 0 TwoVolume.V₁) :
    candidateProfile V=(36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_sphere hV,unit_sphereArea]

lemma candidateProfile_tube {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) :
    candidateProfile V=2*Real.sqrt (Real.pi*V) := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_tube hV]
  rfl

lemma candidateProfile_slab {V : ℝ} (hV : V∈Icc TwoVolume.V₂ (1-TwoVolume.V₂)) :
    candidateProfile V=2 := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_constant hV,mul_one]

lemma CongruentAE.finitePerimeter {E F : Set Torus} (h : CongruentAE E F)
    (hF : FinitePerimeter F) : FinitePerimeter E :=
  ⟨h.nullMeasurableSet hF.1,(h.perimeter_eq hF.1).trans_lt hF.2⟩

theorem SmallStandardRegion.bv_data_oai {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : SmallStandardRegion V E) :
    FinitePerimeter E ∧ torusVolume E=ENNReal.ofReal V ∧
      perimeter E=ENNReal.ofReal (candidateProfile V) := by
  rcases hE with ⟨hsmall,hcong⟩|⟨hlo,hhi,hcong⟩|⟨hlarge,hcong⟩
  · have hF := UpperComparison.finitePerimeter_canonicalBall hV
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (UpperComparison.volume_canonicalBall hV),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalBall_eq hV,
      candidateProfile_sphere ⟨hV.1.le,hsmall⟩]
  · have hF := UpperComparison.finitePerimeter_canonicalTube hV
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (UpperComparison.volume_canonicalTube hV),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalTube_eq hV,
      candidateProfile_tube ⟨hlo,hhi⟩]
  · have h01 : V∈Icc (0 : ℝ) 1 := ⟨hV.1.le,by linarith [hV.2]⟩
    have hF := finitePerimeter_canonicalSlab h01
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (volume_canonicalSlab h01),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalSlab_eq ⟨hV.1,by linarith [hV.2]⟩,
      candidateProfile_slab ⟨hlarge,by linarith [hV.2,TwoVolume.transitions.2.2]⟩]
    norm_num

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.SmallStandardRegion.bv_data_oai := @OAI.CubicTorus.SmallStandardRegion.bv_data_oai
