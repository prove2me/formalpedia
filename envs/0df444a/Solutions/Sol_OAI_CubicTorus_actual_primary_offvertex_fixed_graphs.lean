-- Prove2me | solution 1 for OAI.CubicTorus.actual_primary_offvertex_fixed_graphs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:12:01.059044+00:00
-- url     : https://prove2.me/submissions/833f1f72-9872-4bd6-8957-bd004cf13f19

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_primary_fixed_scale_packets
import Theorems.Thm_OAI_CubicTorus_actual_tangent_secondary_representation
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_moving_limit_comparison
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_secondary_two_sided_density
import Theorems.Thm_OAI_CubicTorus_minimizing_planar_product_halfplane
import Theorems.Thm_OAI_CubicTorus_moving_blowup_perimeter_eq_normal_ball

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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_measurable (n : Cover) : Measurable (normalPlaneEmbedding n) :=
  (normalProductChart n).measurable.comp
    (measurable_const.prodMk (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable)

lemma plane_ball_real {s : ℝ} (hs : 0 ≤ s) :
    (volume : Measure Plane).real (Metric.ball 0 s) = Real.pi * s ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

lemma radialDensityWeight_plane_bound (n : Cover) {s ε : ℝ}
    (hs : 0 ≤ s) (hε : 0 < ε) (y : Plane) :
    ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y := by
  by_cases hy : y ∈ Metric.ball (0 : Plane) s
  · rw [indicator_of_mem hy, Real.norm_eq_abs,
      abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  · rw [indicator_of_notMem hy]
    have hnorm : s ≤ ‖normalPlaneEmbedding n y - 0‖ := by
      simpa only [sub_zero, normalPlaneEmbedding_norm, Metric.mem_ball, dist_zero_right,
        not_lt] using hy
    rw [radialDensityWeight_zero hs hε hnorm, norm_zero]

lemma integral_radialDensityWeight_plane_tendsto (n : Cover) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε : ℝ ↦ ∫ y : Plane, radialDensityWeight 0 s ε (normalPlaneEmbedding n y))
      (𝓝[>] 0) (𝓝 (Real.pi * s ^ 2)) := by
  have hi : Integrable ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator Metric.isOpen_ball.measurableSet
  have ht := tendsto_integral_filter_of_dominated_convergence
    ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)))
    (Eventually.of_forall fun ε : ℝ ↦
      ((radialDensityWeight_contDiff 0 s ε).continuous.measurable.comp
        (normalPlaneEmbedding_measurable n)).aestronglyMeasurable)
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ y : Plane, ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact Eventually.of_forall (radialDensityWeight_plane_bound n hs.le hε)) hi
    (Eventually.of_forall fun y : Plane ↦ radialDensityWeight_tendsto 0 (normalPlaneEmbedding n y) hs)
  have he : (fun y : Plane ↦ (Metric.ball (0 : Cover) s).indicator (fun _ ↦ (1 : ℝ))
      (normalPlaneEmbedding n y)) = (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) := by
    ext y
    have hy : normalPlaneEmbedding n y ∈ Metric.ball (0 : Cover) s ↔
        y ∈ Metric.ball (0 : Plane) s := by
      simp only [Metric.mem_ball, dist_zero_right, normalPlaneEmbedding_norm]
    by_cases h : y ∈ Metric.ball (0 : Plane) s
    · rw [indicator_of_mem h, indicator_of_mem (hy.mpr h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hy.mp h)]
  have hval : (∫ y : Plane, (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y) =
      Real.pi * s ^ 2 := by
    calc _ = (volume : Measure Plane).real (Metric.ball 0 s) :=
          integral_indicator_one Metric.isOpen_ball.measurableSet
         _ = _ := plane_ball_real hs.le
  rw [he, hval] at ht
  exact ht

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
open Laplacian
namespace CubicTorus

lemma normalScalarTest_contDiff (a n : Cover) {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalScalarTest a n χ φ) := by
  exact (hχ.comp (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).mul
    (hφ.comp ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma normalScalarTest_plane_line (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) (u : Plane) (t : ℝ) :
    normalScalarTest a n χ φ (x + t • normalPlaneEmbedding n u) =
      χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a) + t • u) := by
  have he : x + t • normalPlaneEmbedding n u - a =
      (x - a) + t • normalPlaneEmbedding n u := by abel
  rw [normalScalarTest, he, inner_add_right, inner_smul_right,
    normalPlaneEmbedding_inner hn, mul_zero, add_zero, map_add, map_smul,
    normalPlaneCoordinates_embedding]

lemma normalScalarTest_tsupport (a n : Cover) (χ : ℝ → ℝ) (φ : Plane → ℝ) :
    tsupport (normalScalarTest a n χ φ) ⊆
      {x | ⟪n, x - a⟫ ∈ tsupport χ} ∩
        {x | normalPlaneCoordinates n (x - a) ∈ tsupport φ} := by
  apply closure_minimal _
    ((isClosed_closure.preimage (continuous_const.inner (continuous_id.sub continuous_const))).inter
      (isClosed_closure.preimage ((normalPlaneCoordinates n).continuous.comp
        (continuous_id.sub continuous_const))))
  intro x hx
  have hnz : χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) ≠ 0 := hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hnz),
    subset_tsupport _ (right_ne_zero_of_mul hnz)⟩

lemma normalScalarTest_tsupport_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ} {r : ℝ} (hr : 0 < r)
    (hχ : tsupport χ ⊆ Icc (-r / 3) (r / 3))
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    tsupport (normalScalarTest a n χ φ) ⊆ Metric.ball a r := by
  intro x hx
  have hh := normalScalarTest_tsupport a n χ φ hx
  have hv : |⟪n, x - a⟫| ≤ r / 3 := by
    have ht := hχ hh.1
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hp : ‖normalPlaneCoordinates n (x - a)‖ ≤ r / 3 := by
    simpa using hφ hh.2
  have htri := norm_add_le (normalPlaneEmbedding n (normalPlaneCoordinates n (x - a)))
    (⟪n, x - a⟫ • n)
  rw [normalPlaneCoordinates_reconstruct hn, normalPlaneEmbedding_norm, norm_smul,
    Real.norm_eq_abs, hn, mul_one] at htri
  change dist x a < r
  rw [dist_eq_norm]
  linarith

end CubicTorus

end
end

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverLocalPerimeter_mono (A : Set Cover) {O P : Set Cover} (hOP : O ⊆ P) :
    coverLocalPerimeter A O ≤ coverLocalPerimeter A P := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hO
  apply iSup_le
  intro hb
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le (hO.trans hOP) (le_iSup_of_le hb le_rfl))))

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

theorem line_invariant_local_product {B : Set Cover} (hB : MeasurableSet B)
    {n : Cover} (hn : ‖n‖ = 1)
    (htrans : ∀ t : ℝ, |t| ≤ 1/4 → ∀ᵐ x ∂(volume : Measure Cover),
      x ∈ Metric.ball (0 : Cover) (1/4) → (x+t • n ∈ B ↔ x ∈ B)) :
    ∃ C : Set (Fin 2 → ℝ), MeasurableSet C ∧
      ∀ᵐ z : ℝ × (Fin 2 → ℝ) ∂volume,
        |z.1| < 1/16 → ‖normalProductChart n (0,z.2)‖ < 1/16 →
          (normalProductChart n z ∈ B ↔ z.2 ∈ C) := by
  have hm : MeasurableSet {z : Cover × ℝ | |z.2| ≤ 1/4 →
      z.1 ∈ Metric.ball (0 : Cover) (1/4) → (z.1+z.2 • n ∈ B ↔ z.1 ∈ B)} := by
    exact (measurableSet_le measurable_snd.abs measurable_const).imp
      ((Metric.isOpen_ball.measurableSet.preimage measurable_fst).imp
        ((hB.preimage (measurable_fst.add (measurable_snd.smul_const n))).iff
          (hB.preimage measurable_fst)))
  have hx : ∀ᵐ x ∂(volume : Measure Cover), ∀ᵐ t ∂(volume : Measure ℝ),
      |t| ≤ 1/4 → x ∈ Metric.ball (0 : Cover) (1/4) → (x+t • n ∈ B ↔ x ∈ B) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply ae_of_all
    intro t
    by_cases ht : |t| ≤ 1/4
    · exact (htrans t ht).mono (fun x hh _ ↦ hh)
    · exact ae_of_all _ (fun _ hh ↦ (ht hh).elim)
  have hz := (normalProductChart_measurePreserving n).quasiMeasurePreserving.ae hx
  have hsplit := Measure.ae_ae_of_ae_prod hz
  have hrel : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ y : Fin 2 → ℝ ∂volume,
      ∀ᵐ t ∂(volume : Measure ℝ), |s| < 1/16 →
        ‖normalProductChart n (0,y)‖ < 1/16 → |t| < 1/16 →
          (normalProductChart n (t,y) ∈ B ↔ normalProductChart n (s,y) ∈ B) := by
    filter_upwards [hsplit] with s hs
    filter_upwards [hs] with y hy
    have ht := (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae hy
    filter_upwards [ht] with t hh hs0 hy0 ht0
    have hts : |t+-s| ≤ 1/4 := (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
    have hxb : normalProductChart n (s,y) ∈ Metric.ball (0 : Cover) (1/4) := by
      rw [Metric.mem_ball,dist_zero_right,normalProductChart_decompose hn]
      exact (norm_add_le _ _).trans_lt (by rw [norm_smul,Real.norm_eq_abs,hn,mul_one]; linarith)
    have heq : normalProductChart n (s,y)+(t+-s) • n = normalProductChart n (t,y) := by
      rw [normalProductChart_decompose hn s y,normalProductChart_decompose hn t y]
      module
    simpa only [heq] using hh hts hxb
  have hpos : (volume : Measure ℝ) (Ioo (-(1/16 : ℝ)) (1/16)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hrel)
  have hs0 : |s| < 1/16 := abs_lt.mpr hsI
  let C : Set (Fin 2 → ℝ) := {y | normalProductChart n (s,y) ∈ B}
  have hC : MeasurableSet C := hB.preimage
    ((normalProductChart n).measurable.comp (measurable_const.prodMk measurable_id))
  refine ⟨C,hC,?_⟩
  have hm' : MeasurableSet {z : (Fin 2 → ℝ) × ℝ | |z.2| < 1/16 →
      ‖normalProductChart n (0,z.1)‖ < 1/16 →
        (normalProductChart n (z.2,z.1) ∈ B ↔ z.1 ∈ C)} := by
    exact (measurableSet_lt measurable_snd.abs measurable_const).imp
      ((measurableSet_lt (((normalProductChart n).measurable.comp
        (measurable_const.prodMk measurable_fst)).norm) measurable_const).imp
        ((hB.preimage ((normalProductChart n).measurable.comp measurable_swap)).iff
          (hC.preimage measurable_fst)))
  apply (Measure.ae_prod_iff_ae_ae (hm'.preimage measurable_swap)).mpr
  apply (Measure.ae_ae_comm hm').mp
  filter_upwards [hs] with y hy
  filter_upwards [hy] with t ht ht0 hy0
  exact ht hs0 hy0 ht0

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma moving_blowup_flux_tendsto {E : Set Torus} (hE : MeasurableSet E)
    (c : ℕ → Cover) (r : ℕ → ℝ) {A : Set Cover} (hA : MeasurableSet A)
    {R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) R) :
    Tendsto (fun i ↦ ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x)
      l (𝓝 (∫ x in A, divergence F x)) := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hd : HasCompactSupport (divergence F) := hFs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  let k : Cover →ᵇ ℝ := ofCompactSupport _ (continuous_divergence hF) hd
  have ht := localL1_weighted_integral_tendsto
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv k
  have hz (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) R) : divergence F x = 0 :=
    divergence_of_notMem_tsupport (fun hh ↦ hx (hs hh))
  have heg (i) : (∫ x in Metric.closedBall (0 : Cover) R, blowupCharacteristic E (c i) (r i) x*k x) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])
  have hef : (∫ x in Metric.closedBall (0 : Cover) R, A.indicator (fun _ ↦ (1 : ℝ)) x*k x) =
      ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])]
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence F x) = _
    simp only [← indicator_mul_left,one_mul]
    exact integral_indicator hA
  simpa only [heg,hef] using ht

lemma blowup_flux_le_scaled_mass {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r a : ℝ} (hr : 0 < r) (ha : a ≤ 1)
    (hc : Metric.closedBall c r ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.ball (0 : Cover) a) (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x, blowupCharacteristic E c r x*divergence F x) ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap c) (r*a))/r^2 := by
  have hs1 := hs.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ha))
  have he := normalMeasure_scaled_flux hE hμ hF hs1 c hr hc
  rw [show (fun x ↦ characteristic E (quotientMap (r • x+c))*divergence F x) =
      (fun x ↦ blowupCharacteristic E c r x*divergence F x) by funext x; simp only [blowupCharacteristic,add_comm c]] at he
  rw [← he]
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball c (r*a)}
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.preimage (by fun_prop)
  have hchart : Metric.ball c (r*a) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by nlinarith))).trans hc
  rw [← cellBallMass_eq_spatialNormalMeasure μ c (r*a) hchart]
  change _ ≤ (μ : Measure NormalBundle).real S
  let f : NormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F (r⁻¹ • ((z.1 : Cover)-c))⟫
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfi : Integrable f (μ : Measure NormalBundle) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (μ : Measure NormalBundle) := (integrable_const 1).indicator hS
  have hfbd (z : NormalBundle) : f z ≤ S.indicator (fun _ ↦ (1 : ℝ)) z := by
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      exact (real_inner_le_norm _ _).trans (by rw [z.2.property,one_mul]; exact hb _)
    · rw [indicator_of_notMem hz]
      have hx : r⁻¹ • ((z.1 : Cover)-c) ∉ tsupport F := by
        intro hh
        have hnorm : ‖(z.1 : Cover)-c‖/r < a := by
          simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hs hh
        exact hz (by change dist (z.1 : Cover) c < r*a; rw [dist_eq_norm]; nlinarith [(div_lt_iff₀ hr).mp hnorm])
      simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right,le_refl]
  have hh := integral_mono hfi hgi hfbd
  simpa only [integral_indicator hS,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma affineScalarTest_contDiff {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (p : Cover) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (affineScalarTest p r ψ) :=
  hψ.comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma affineScalarTest_tsupport {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1)
    (p : Cover) {r : ℝ} (hr : 0 < r) :
    tsupport (affineScalarTest p r ψ) ⊆ Metric.closedBall p r := by
  have hc : Continuous (fun x : Cover ↦ r⁻¹ • (x-p)) := by fun_prop
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ hc hx)
  have hh' : ‖x-p‖ / r ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hh
  simpa only [Metric.mem_closedBall,dist_eq_norm] using (div_le_iff₀ hr).mp hh' |>.trans_eq (one_mul r)

lemma fderiv_affineScalarTest {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ)
    (p : Cover) {r : ℝ} (hr : r ≠ 0) (x v : Cover) :
    fderiv ℝ (affineScalarTest p r ψ) (r • x+p) v = r⁻¹ * fderiv ℝ ψ x v := by
  have hd := (hψ (r⁻¹ • ((r • x+p)-p))).hasFDerivAt.comp (r • x+p)
    (((hasFDerivAt_id (r • x+p)).sub_const p).const_smul (r⁻¹))
  change HasFDerivAt (affineScalarTest p r ψ) _ (r • x+p) at hd
  rw [hd.fderiv]
  simp [hr]

lemma affineScalarTest_radial {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ)
    (p : Cover) {r : ℝ} (hr : r ≠ 0) (x : Cover) :
    3*affineScalarTest p r ψ (r • x+p) +
      fderiv ℝ (affineScalarTest p r ψ) (r • x+p) (r • x+p) =
      r⁻¹ * (fderiv ℝ ψ x p + r*(3*ψ x+fderiv ℝ ψ x x)) := by
  rw [fderiv_affineScalarTest hψ p hr]
  simp only [affineScalarTest,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hr,one_smul,
    map_add,map_smul,smul_eq_mul]
  field_simp
  ring

lemma radial_flux_affine_identity {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1)
    (p : Cover) {r : ℝ} (hr : 0 < r)
    (hpr : Metric.closedBall p r ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p) *
      (fderiv ℝ ψ x p+r*(3*ψ x+fderiv ℝ ψ x x))) = 0 := by
  have he := hrad _ (affineScalarTest_contDiff hψ p r)
    ((affineScalarTest_tsupport hs p hr).trans hpr)
  rw [← integral_indicator hA] at he
  have hid : A.indicator (fun x ↦ 3*affineScalarTest p r ψ x+
      fderiv ℝ (affineScalarTest p r ψ) x x) =
      fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) x *
        (3*affineScalarTest p r ψ x+fderiv ℝ (affineScalarTest p r ψ) x x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hid,integral_cover_affine_scaling _ p hr] at he
  simp_rw [affineScalarTest_radial (hψ.differentiable (by simp)) p hr.ne',
    show ∀ a b : ℝ, a*(r⁻¹*b)=r⁻¹*(a*b) by intros; ring] at he
  rw [integral_const_mul] at he
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hr.ne'))).resolve_left (inv_ne_zero hr.ne')

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma local_indicator_pairing_tendsto {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (p : Cover) (r : ℕ → ℝ) {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {f : Cover → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ Metric.closedBall (0 : Cover) 1) :
    Tendsto (fun i ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*f x)
      l (𝓝 (∫ x in B, f x)) := by
  have hfs : HasCompactSupport f := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  let k : Cover →ᵇ ℝ := ofCompactSupport f hf hfs
  have hm (i) : Measurable (fun x : Cover ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)) :=
    (measurable_const.indicator hA).comp (by fun_prop)
  have hb (C : Set Cover) (x : Cover) : |C.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ C <;> simp [hx]
  have hh := localL1_weighted_integral_tendsto _ hm (fun i x ↦ hb A _)
    (measurable_const.indicator hB) (hb B) hconv k
  have hzero (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) 1) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have he (g : Cover → ℝ) : (∫ x in Metric.closedBall (0 : Cover) 1, g x*k x) = ∫ x, g x*f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      change g x*f x = 0
      rw [hzero x hx,mul_zero])
  simp_rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [← indicator_mul_left,one_mul,integral_indicator hB]

lemma fderiv_apply_tsupport_subset {ψ : Cover → ℝ} (p : Cover) :
    tsupport (fun x ↦ fderiv ℝ ψ x p) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by change fderiv ℝ ψ x p = 0; rw [fderiv_of_notMem_tsupport ℝ h]; rfl)

lemma radial_euler_tsupport_subset {ψ : Cover → ℝ} :
    tsupport (fun x ↦ 3*ψ x+fderiv ℝ ψ x x) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by change 3*ψ x+fderiv ℝ ψ x x = 0; rw [image_eq_zero_of_notMem_tsupport h,fderiv_of_notMem_tsupport ℝ h]; simp)

lemma indicator_pairing_integrable {A : Set Cover} (hA : MeasurableSet A)
    {f : Cover → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    (p : Cover) (r : ℝ) :
    Integrable (fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)*f x) := by
  have hm : AEStronglyMeasurable (fun x : Cover ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)) volume :=
    ((measurable_const.indicator hA).comp (by fun_prop)).aestronglyMeasurable
  have hi := (hf.integrable_of_hasCompactSupport hs).mul_bdd hm (ae_of_all _ fun x ↦ cover_indicator_bound A _)
  simpa only [mul_comm] using hi

theorem radial_cone_secondary_derivative_zero {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ x in B, fderiv ℝ ψ x p) = 0 := by
  have hc0 : Continuous (fun x ↦ fderiv ℝ ψ x p) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc1 : Continuous (fun x ↦ 3*ψ x+fderiv ℝ ψ x x) :=
    (hψ.continuous.const_mul 3).add ((hψ.continuous_fderiv (by simp)).clm_apply continuous_id)
  have hs0 := (fderiv_apply_tsupport_subset (ψ:=ψ) p).trans hs
  have hs1 := (radial_euler_tsupport_subset (ψ:=ψ)).trans hs
  have hl0 := local_indicator_pairing_tendsto hA hB p r hconv hc0 hs0
  have hl1 := local_indicator_pairing_tendsto hA hB p r hconv hc1 hs1
  have hl := hl0.add (hrlim.mul hl1)
  simp only [zero_mul,add_zero] at hl
  have he : (fun i ↦ (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*fderiv ℝ ψ x p) +
      r i*(∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*(3*ψ x+fderiv ℝ ψ x x))) =ᶠ[l] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    have hball : Metric.closedBall p (r i) ⊆ Metric.ball (0 : Cover) 1 := by
      intro x hx
      have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
      have hn := norm_add_le (x-p) p
      rw [sub_add_cancel] at hn
      simpa only [Metric.mem_ball,dist_zero_right] using (by linarith : ‖x‖ < 1)
    have hid := radial_flux_affine_identity hA hrad hψ hs p (hr i) hball
    have hi0 := indicator_pairing_integrable hA hc0 ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs0) p (r i)
    have hi1 := indicator_pairing_integrable hA hc1 ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs1) p (r i)
    have hmul (x : Cover) : A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p) *
        (fderiv ℝ ψ x p+r i*(3*ψ x+fderiv ℝ ψ x x)) =
        A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*fderiv ℝ ψ x p+
          r i*(A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*(3*ψ x+fderiv ℝ ψ x x)) := by ring
    simp_rw [hmul] at hid
    rwa [integral_add hi0 (hi1.const_mul _),integral_const_mul] at hid
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' he.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma hasDerivAt_setIntegral_translation {B : Set Cover} (hB : MeasurableSet B)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ)
    (v : Cover) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+s • v))
      (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (x+t • v) v) t := by
  let η : Measure Cover := volume.restrict (B ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hψ.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  have hm (s : ℝ) : AEStronglyMeasurable (fun x ↦ ψ (x+s • v)) η :=
    (hψ.continuous.comp (by fun_prop)).continuousOn.aestronglyMeasurable
      (hB.inter Metric.isClosed_closedBall.measurableSet)
  have hi : Integrable (fun x ↦ ψ (x+t • v)) η :=
    Integrable.of_bound (hm t) M (ae_of_all _ fun x ↦ hM _)
  have hm' : AEStronglyMeasurable (fun x ↦ fderiv ℝ ψ (x+t • v) v) η :=
    (((hψ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable
  have hb : ∀ᵐ x ∂η, ∀ s ∈ (univ : Set ℝ), ‖fderiv ℝ ψ (x+s • v) v‖ ≤ |K| * ‖v‖ :=
    ae_of_all _ fun x s _ ↦ (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((hK _).trans (le_abs_self K)) (norm_nonneg _))
  have hd (x : Cover) (s : ℝ) : HasDerivAt (fun u : ℝ ↦ ψ (x+u • v)) (fderiv ℝ ψ (x+s • v) v) s := by
    convert! (hψ.differentiable (by simp) (x+s • v)).hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const v).const_add x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_smul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (univ_mem : univ ∈ 𝓝 t)
    (Eventually.of_forall hm) hi hm' hb (integrable_const (|K| * ‖v‖))
    (ae_of_all _ fun x s _ ↦ hd x s)).2

lemma translation_test_tsupport {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) (1/4)) {v : Cover} (hv : ‖v‖ ≤ 1/4)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tsupport (fun x ↦ ψ (x+t • v)) ⊆ Metric.ball (0 : Cover) (1/2) := by
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun x : Cover ↦ x+t • v)) hx)
  have hx' : ‖x+t • v‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have htv : ‖t • v‖ ≤ 1/4 := by
    rw [norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans (by simpa only [one_mul] using hv)
  have hh := norm_sub_le (x+t • v) (t • v)
  rw [add_sub_cancel_right] at hh
  simpa only [Metric.mem_ball,dist_zero_right] using (by linarith : ‖x‖ < 1/2)

lemma derivative_zero_translation_pairing {B : Set Cover} (hB : MeasurableSet B) (v : Cover)
    (hv : ‖v‖ ≤ 1/4)
    (hzero : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1 → (∫ x in B, fderiv ℝ ψ x v) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) (1/4)) :
    (∫ x, ψ x*B.indicator (fun _ ↦ (1 : ℝ)) (x-v)) =
      ∫ x, ψ x*B.indicator (fun _ ↦ (1 : ℝ)) x := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun t ↦ ∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+t • v)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt I 0 t := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (x+t • v)) :=
      hψ.comp (contDiff_id.add contDiff_const)
    have hts := (translation_test_tsupport hs hv ht).trans
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1/2 : ℝ) ≤ 1)))
    have hef (x : Cover) : fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v = fderiv ℝ ψ (x+t • v) v := by
      have hh := (hψ.differentiable (by simp) (x+t • v)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const (t • v))
      change HasFDerivAt (fun y : Cover ↦ ψ (y+t • v)) _ x at hh
      simp only [hh.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
    have hz := hzero _ hcomp hts
    have heq : (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v) =
        ∫ x in B, fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v := by
      rw [inter_comm B,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hts hh))]
      rfl
    rw [← heq] at hz
    simp_rw [hef] at hz
    exact (hasDerivAt_setIntegral_translation hB hψ hψs v t).congr_deriv hz
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (hd t ht).hasDerivWithinAt)
    (fun _ _ ↦ by simp : ∀ t ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ)‖ ≤ 0) (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have heI : I 1=I 0 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : I t = ∫ x, ψ (x+t • v)*B.indicator (fun _ ↦ (1 : ℝ)) x := by
    change (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+t • v)) = _
    rw [inter_comm B,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1) (translation_test_tsupport hs hv ht hh)))))]
    rw [← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [he 1 (by norm_num),he 0 (by norm_num)] at heI
  simp only [one_smul,zero_smul,add_zero] at heI
  have htrans := integral_add_right_eq_self (μ := (volume : Measure Cover)) (fun x : Cover ↦ ψ x*B.indicator (fun _ ↦ (1 : ℝ)) (x-v)) v
  simp only [add_sub_cancel_right] at htrans
  exact htrans.symm.trans heI

theorem derivative_zero_translation_ae {B : Set Cover} (hB : MeasurableSet B) (v : Cover)
    (hv : ‖v‖ ≤ 1/4)
    (hzero : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1 → (∫ x in B, fderiv ℝ ψ x v) = 0) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x-v ∈ B ↔ x ∈ B) := by
  let f : Cover → ℝ := B.indicator (fun _ ↦ 1)
  have hm : Measurable f := measurable_const.indicator hB
  have hm' : Measurable (fun x : Cover ↦ f (x-v)) := hm.comp (by fun_prop)
  have hb (x : Cover) : ‖f x‖ ≤ 1 := cover_indicator_bound B x
  have hli : LocallyIntegrable f (volume : Measure Cover) :=
    (memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).locallyIntegrable le_top
  have hli' : LocallyIntegrable (fun x : Cover ↦ f (x-v)) (volume : Measure Cover) :=
    (memLp_top_of_bound hm'.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ hb _)).locallyIntegrable le_top
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hli'.sub hli).locallyIntegrableOn (Metric.ball (0 : Cover) (1/4))) (fun ψ hψ hψs hs ↦ ?_)
  · filter_upwards [hz] with x hx hxin
    have he : f (x-v)=f x := sub_eq_zero.mp (hx hxin)
    by_cases h1 : x-v ∈ B <;> by_cases h2 : x ∈ B <;> simp [f,h1,h2] at he ⊢
  · have hi : Integrable ψ (volume : Measure Cover) := hψ.continuous.integrable_of_hasCompactSupport hψs
    have hi1 := hi.mul_bdd hm'.aestronglyMeasurable (ae_of_all _ fun x ↦ hb (x-v))
    have hi2 := hi.mul_bdd hm.aestronglyMeasurable (ae_of_all _ hb)
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub,integral_sub hi1 hi2]
    exact sub_eq_zero.mpr (derivative_zero_translation_pairing hB v hv hzero hψ hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem radial_cone_secondary_line_invariance {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    (t : ℝ) (ht : |t| * ‖p‖ ≤ 1/4) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x+t • p ∈ B ↔ x ∈ B) := by
  have hz (ψ : Cover → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1) :
      (∫ x in B, fderiv ℝ ψ x (-(t • p))) = 0 := by
    simp only [map_neg,map_smul,smul_eq_mul,integral_neg,integral_const_mul]
    rw [radial_cone_secondary_derivative_zero hA hB hrad p hp r hr hrlim hconv hψ hs,mul_zero,neg_zero]
  have hv : ‖-(t • p)‖ ≤ 1/4 := by simpa only [norm_neg,norm_smul,Real.norm_eq_abs] using ht
  simpa only [sub_neg_eq_add] using derivative_zero_translation_ae hB (-(t • p)) hv hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cone_dilation_pairing {A : Set Cover} (hA : MeasurableSet A)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    {t : ℝ} (ht : 1 ≤ t) :
    t^3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ x := by
  have he : (∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) =
      ∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) x := by
    apply integral_congr_ae
    filter_upwards [hcone t ht] with x hx
    by_cases hb : x ∈ Metric.ball (0 : Cover) 1
    · by_cases ha : x ∈ A
      · simp only [indicator_of_mem ha,indicator_of_mem ((hx hb).mpr ha)]
      · simp only [indicator_of_notMem ha,indicator_of_notMem (mt (hx hb).mp ha)]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hb (hs hh)),zero_mul,zero_mul]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hscale := integral_cover_affine_scaling
    (fun x : Cover ↦ ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) 0 ht0
  simp only [add_zero,smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hscale
  rw [hscale,integral_indicator_dilation_local hA hs ht] at he
  have he1 := integral_indicator_dilation_local hA hs (t := 1) le_rfl
  simp only [one_smul] at he1
  exact he.trans he1

theorem cone_radial_euler {A : Set Cover} (hA : MeasurableSet A)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0 := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun t ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)
  let J : ℝ := ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ x x
  have hdI : HasDerivAt I J 1 := by
    simpa only [I,J,one_smul] using hasDerivAt_setIntegral_dilation hA hψ hψs 1
  have hdP : HasDerivAt (fun t : ℝ ↦ t^3*I t) (3*I 1+J) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).pow 3).mul hdI).congr_deriv (show
      (3 : ℝ)*1^(3-1)*1*I 1+1^3*J = 3*I 1+J by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
  have hc : HasDerivWithinAt (fun t : ℝ ↦ t^3*I t) 0 (Ici 1) 1 :=
    (hasDerivWithinAt_const 1 (Ici (1 : ℝ)) (I 1)).congr
      (fun t ht ↦ by
        have hh := cone_dilation_pairing hA hcone hs ht
        simpa only [I,one_smul] using hh)
      (by norm_num)
  have he : 3*I 1+J=0 :=
    (hdP.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 1)).symm.trans
      (hc.derivWithin (uniqueDiffWithinAt_Ici 1))
  have hi : IntegrableOn ψ (A ∩ Metric.closedBall (0 : Cover) 1) :=
    (hψ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set inter_subset_right
  have hdi : IntegrableOn (fun x ↦ fderiv ℝ ψ x x) (A ∩ Metric.closedBall (0 : Cover) 1) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_id).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set inter_subset_right
  have heq : (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, 3*ψ x+fderiv ℝ ψ x x := by
    rw [inter_comm A,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport ψ := fun hh ↦ hx (Metric.ball_subset_closedBall (hs hh))
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn]
    simp
  rw [heq,integral_add (hi.const_mul 3) hdi,integral_const_mul]
  simpa only [I,J,one_smul] using he

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVStationaryDensity
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

theorem isMinimizerAt_moving_limit_perimeter {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ M : ℝ, 0 < M ∧ ∀ (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ),
      (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A → ∀ R : ℝ,
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ b : ℝ, 0 < b → b ≤ 1 → b ≤ R →
      coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤ ENNReal.ofReal (M*b^2) := by
  obtain ⟨S,M,hS,hM,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  refine ⟨M,hM,?_⟩
  intro c r hr hrlim A hA R hconv b hb hb1 hbR
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hFs
  apply iSup_le
  intro hs
  apply iSup_le
  intro hn
  have hsmall : ∀ᶠ i in atTop, r i < 3/8 ∧ r i*b < S := by
    have ht : Tendsto (fun i ↦ r i*b) atTop (𝓝 0) := by simpa using hrlim.mul_const b
    exact (hrlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<3/8))).and
      (ht.eventually (gt_mem_nhds hS))
  have hineq : ∀ᶠ i in atTop, (∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x) ≤ M*b^2 := by
    filter_upwards [hsmall] with i hi
    apply (blowup_flux_le_scaled_mass hE hμ (c i) (hr i) hb1
      (MovingCenter.closedBall_interior hi.1) hF hs hn).trans
    apply (div_le_iff₀ (sq_pos_of_pos (hr i))).mpr
    exact (harea μ hμ _ _ (mul_pos (hr i) hb) hi.2.le).trans_eq (by ring)
  have ht := moving_blowup_flux_tendsto hE (fun i ↦ (c i : Cover)) r hA hconv hF
    (hs.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)))
  exact ENNReal.ofReal_le_ofReal (le_of_tendsto ht hineq)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radial_cone_secondary_unit_line {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    (t : ℝ) (ht : |t| ≤ 1/4) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x+t • (‖p‖⁻¹ • p) ∈ B ↔ x ∈ B) := by
  have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  have ht' : |t*‖p‖⁻¹| * ‖p‖ ≤ 1/4 := by
    simpa only [abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),mul_assoc,
      inv_mul_cancel₀ hpn,mul_one] using ht
  simpa only [smul_smul,add_comm] using radial_cone_secondary_line_invariance hA hB
    (fun ψ hψ hs ↦ cone_radial_euler hA hcone hψ hs) p hp r hr hrlim
      (by simpa only [add_comm] using hconv) (t*‖p‖⁻¹) ht'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalScalarTest_plane_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) (u : Plane) :
    fderiv ℝ (normalScalarTest a n χ φ) x (normalPlaneEmbedding n u) =
      χ ⟪n,x-a⟫*fderiv ℝ φ (normalPlaneCoordinates n (x-a)) u := by
  have hf := normalScalarTest_contDiff a n hχ hφ
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • normalPlaneEmbedding n u)
      (normalPlaneEmbedding n u) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (normalPlaneEmbedding n u)).const_add x
  have hd := ((hf.differentiable (by simp)) (x+(0 : ℝ) • normalPlaneEmbedding n u)).hasFDerivAt.comp_hasDerivAt 0 hl
  have hl' : HasDerivAt (fun t : ℝ ↦ normalPlaneCoordinates n (x-a)+t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (normalPlaneCoordinates n (x-a))
  have hd' := (((hφ.differentiable (by simp)) (normalPlaneCoordinates n (x-a)+(0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt 0 hl').const_mul (χ ⟪n,x-a⟫)
  have he : (fun t : ℝ ↦ normalScalarTest a n χ φ (x+t • normalPlaneEmbedding n u)) =
      (fun t : ℝ ↦ χ ⟪n,x-a⟫*φ (normalPlaneCoordinates n (x-a)+t • u)) :=
    funext (normalScalarTest_plane_line a hn χ φ x u)
  have hd0 : HasDerivAt (fun t : ℝ ↦ normalScalarTest a n χ φ (x+t • normalPlaneEmbedding n u))
      (fderiv ℝ (normalScalarTest a n χ φ) x (normalPlaneEmbedding n u)) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero] using hd
  rw [he] at hd0
  simpa using hd0.unique hd'

lemma divergence_planar_product_test {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (u : Plane) (x : Cover) :
    divergence (fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u) x =
      χ ⟪n,x⟫*fderiv ℝ φ (normalPlaneCoordinates n x) u := by
  rw [divergence_smul_const ((normalScalarTest_contDiff 0 n hχ hφ).differentiable (by simp) x),
    normalScalarTest_plane_derivative 0 hn hχ hφ]
  simp only [sub_zero]

lemma line_product_euclidean {B : Set Cover} {C : Set (Fin 2 → ℝ)} (hC : MeasurableSet C)
    {n : Cover}
    (hprod : ∀ᵐ z : ℝ × (Fin 2 → ℝ) ∂volume,
      |z.1| < 1/16 → ‖normalProductChart n (0,z.2)‖ < 1/16 →
        (normalProductChart n z ∈ B ↔ z.2 ∈ C)) :
    ∃ D : Set Plane, MeasurableSet D ∧
      ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
        (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ D) := by
  let D : Set Plane := WithLp.ofLp ⁻¹' C
  have hm : MeasurePreserving (fun z : ℝ × Plane ↦ (z.1,WithLp.ofLp z.2)) := by
    change MeasurePreserving (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
    simpa only [Measure.volume_eq_prod] using (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  refine ⟨D,hC.preimage (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable,?_⟩
  filter_upwards [hm.quasiMeasurePreserving.ae hprod] with z hz ht hy
  have hy' : ‖normalProductChart n (0,WithLp.ofLp z.2)‖ < 1/16 := by
    change ‖normalPlaneEmbedding n z.2‖ < 1/16
    rwa [normalPlaneEmbedding_norm]
  change 0+normalProductChart n (z.1,WithLp.ofLp z.2) ∈ B ↔ WithLp.ofLp z.2 ∈ C
  rw [zero_add]
  exact hz ht hy'

theorem planar_product_flux {B : Set Cover} {C : Set Plane} (hB : MeasurableSet B)
    (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsχ : tsupport χ ⊆ Icc (-(1/32 : ℝ)) (1/32))
    (hsφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32)) (u : Plane) :
    (∫ x in B, divergence (fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u) x) =
      (∫ t, χ t)*(∫ y in C, fderiv ℝ φ y u) := by
  let F : Cover → Cover := fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u
  rw [← integral_indicator hB]
  rw [← (normalColumnChart_measurePreserving 0 n).integral_comp']
  change (∫ z : ℝ × Plane, B.indicator (divergence F) (normalColumnChart 0 n z)) = _
  have he : (fun z : ℝ × Plane ↦ B.indicator (divergence F) (normalColumnChart 0 n z)) =ᵐ[volume]
      (fun z ↦ χ z.1*C.indicator (fun y ↦ fderiv ℝ φ y u) z.2) := by
    filter_upwards [hprod] with z hz
    have hdiv : divergence F (normalColumnChart 0 n z) = χ z.1*fderiv ℝ φ z.2 u := by
      rw [divergence_planar_product_test hn hχ hφ]
      rw [← sub_zero (normalColumnChart 0 n z),normalColumnChart_height 0 hn,
        normalColumnChart_projection 0 hn]
    by_cases ht : |z.1| < 1/16
    · by_cases hy : ‖z.2‖ < 1/16
      · by_cases hc : z.2 ∈ C
        · rw [indicator_of_mem ((hz ht hy).mpr hc),indicator_of_mem hc,hdiv]
        · rw [indicator_of_notMem hc,mul_zero,indicator_of_notMem (mt (hz ht hy).mp hc)]
      · have hnot : z.2 ∉ tsupport φ := by
          intro hh
          have hh' : ‖z.2‖ ≤ 1/32 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hsφ hh
          exact hy (by linarith)
        have hd : fderiv ℝ φ z.2 u = 0 := by rw [fderiv_of_notMem_tsupport ℝ hnot]; rfl
        simp only [hd,mul_zero] at hdiv
        by_cases hc : z.2 ∈ C <;> by_cases hb : normalColumnChart 0 n z ∈ B <;>
          simp [hc,hb,hdiv,hd]
    · have hc : χ z.1 = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hh
        have h := hsχ hh
        exact ht (abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩))
      simp only [hc,zero_mul] at hdiv ⊢
      by_cases hb : normalColumnChart 0 n z ∈ B <;> simp [hb,hdiv]
  rw [integral_congr_ae he,Measure.volume_eq_prod,integral_prod_mul,integral_indicator hC]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weakCMC_moving_blowup_limit_stationary {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupTangentTest hF hFs)
  have hf := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupFluxTest hF.continuous hFs)
  have hh := (hrlim.mul_const H).mul hf
  simp only [zero_mul] at hh
  have he (i) := weakCMC_blowup_identity hμ hH hF hs (c i) (hr i) hR (hc i)
  exact tendsto_nhds_unique ht (hh.congr (fun i ↦ (he i).symm))

theorem moving_blowup_normal_limit_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ x in A, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hf := moving_blowup_flux_tendsto hE c r hA hconv hF hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (blowupFluxTest hF.continuous hFs)
  have he (i) : (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(blowupNormalMeasure μ (c i) (r i) R : Measure BlowupNormalBundle)) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x := by
    rw [integral_blowup_test μ (c i) (hr i) (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by
        have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
        simp [image_eq_zero_of_notMem_tsupport hn])]
    change (r i)⁻¹^2*(∫ z, ⟪(z.2 : Cover),F ((r i)⁻¹ • ((z.1 : Cover)-c i))⟫ ∂(μ : Measure NormalBundle)) = _
    rw [show (r i)⁻¹^2 = ((r i)^2)⁻¹ by ring]
    rw [← div_eq_inv_mul,normalMeasure_scaled_flux hE hμ hF hs (c i) (hr i) (hc i)]
    simp only [blowupCharacteristic,add_comm (c i)]
  exact tendsto_nhds_unique (hweak.congr fun i ↦ he i) hf

theorem moving_blowup_normal_cluster {μ : FiniteMeasure NormalBundle}
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, cellBallMass μ (c i) (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) := by
  have hm (i) : (blowupNormalMeasure μ (c i) (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,blowupNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,blowupNormalMeasure_supported μ (c i) (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

theorem isMinimizerAt_moving_paired_normal_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0)) {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ (ν : FiniteMeasure BlowupNormalBundle) (k : ℕ) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ (c (i+k)) (r (i+k)) 2) U (𝓝 ν) ∧
      ν ((Metric.closedBall (0 : Cover) 2 ×ˢ univ)ᶜ) = 0 ∧
      ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x := by
  obtain ⟨S,B,hS,hB,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hsmall : 0 < min (3/16 : ℝ) (S/2) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let q : ℕ → ℝ := fun i ↦ r (i+k)
  let d : ℕ → Cover := fun i ↦ c (i+k)
  have hq (i) : 0 < q i := hr _
  have hqb (i) : q i < min (3/16 : ℝ) (S/2) := hk _ (by omega)
  have hchart (i) : Metric.closedBall (d i) (q i*2) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    MovingCenter.closedBall_interior (c := c (i+k)) (by
      have hh := (hqb i).trans_le (min_le_left _ _)
      linarith)
  have hmass (i) : cellBallMass μ (d i) (q i*2) ≤ (B*4)*(q i)^2 := by
    rw [cellBallMass_eq_spatialNormalMeasure μ (d i) _ (Metric.ball_subset_closedBall.trans (hchart i))]
    have hh := harea μ hμ (quotientMap (d i)) (q i*2) (mul_pos (hq i) (by norm_num)) (by
      have hh := (hqb i).trans_le (min_le_right _ _)
      linarith)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨ν,_,hsup,hcl⟩ := moving_blowup_normal_cluster d q hq (by positivity : 0 ≤ B*4) hmass
  obtain ⟨U,hU,hν⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hqlim : Tendsto q (U : Filter ℕ) (𝓝 0) :=
    (hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hc1 (i) : Metric.closedBall (d i) (q i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.closedBall_subset_closedBall (by have hh := hq i; linarith)).trans (hchart i)
  have hconv' : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (d i) (q i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        (U : Filter ℕ) (𝓝 0) := (hconv.comp (tendsto_add_atTop_nat k)).mono_left hU
  refine ⟨ν,k,U,hU,hν,hsup,?_⟩
  intro F hF hs
  exact ⟨weakCMC_moving_blowup_limit_stationary hμ hH d q hq (by norm_num) hc1 hqlim hν hF hs,
    moving_blowup_normal_limit_flux hE hμ d q hq (by norm_num) hc1 hν hA hconv' hF hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_euclideanRadialWeight (μ : FiniteMeasure BlowupNormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensityWeight a r ε z.1) (μ : Measure BlowupNormalBundle) := by
  apply Integrable.of_bound (((radialDensityWeight_contDiff a r ε).continuous.comp continuous_fst).measurable.aestronglyMeasurable) 1
  exact ae_of_all _ (fun z ↦ by
    change |radialDensityWeight a r ε z.1| ≤ 1
    rw [abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _)

lemma integrable_euclideanRadialSlope (μ : FiniteMeasure BlowupNormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensitySlope a r ε z.1) (μ : Measure BlowupNormalBundle) := by
  obtain ⟨K, _, hK⟩ := smoothTransition_exists_deriv_bound
  apply Integrable.of_bound (((continuous_radialDensitySlope a r ε).comp continuous_fst).measurable.aestronglyMeasurable) (K/|ε|)
  apply ae_of_all
  intro z
  change |radialDensitySlope a r ε z.1| ≤ K/|ε|
  simp only [radialDensitySlope,abs_div]
  exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hK ((r^2-‖z.1-a‖^2)/ε)) (abs_nonneg _)

lemma hasDerivAt_euclideanRadialMass (μ : FiniteMeasure BlowupNormalBundle) (a : Cover)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (euclideanRadialMass μ a ε)
      (∫ z, 2 * r * radialDensitySlope a r ε z.1 ∂(μ : Measure BlowupNormalBundle)) r := by
  obtain ⟨K, hK, hb⟩ := smoothTransition_exists_deriv_bound
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ radialDensityWeight a s ε z.1) (μ : Measure BlowupNormalBundle) :=
    (integrable_euclideanRadialWeight μ a s ε).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ 2 * r * radialDensitySlope a r ε z.1) (μ : Measure BlowupNormalBundle) :=
    ((integrable_euclideanRadialSlope μ a r ε).const_mul _).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂(μ : Measure BlowupNormalBundle), ∀ s ∈ Ioo (r - 1) (r + 1),
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
    (integrable_euclideanRadialWeight μ a r ε) hm' hb' (integrable_const _)
    (Eventually.of_forall fun z s _ ↦ hasDerivAt_radialDensityWeight a z.1 s ε)).2

theorem stationary_euclideanRadialMass_ode {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hc : Metric.closedBall a r ⊆ Metric.closedBall (0 : Cover) 1) :
    2 * euclideanRadialMass ν a ε r ≤ r * deriv (euclideanRadialMass ν a ε) r := by
  let F := radialDensityField a r ε
  have hf := radialDensityField_contDiff a r ε
  have hs := radialDensityField_hasCompactSupport (a := a) hr.le hε
  have hid := hstat F hf ((radialDensityField_tsupport hr.le hε).trans hc)
  have ht : Integrable (fun z : BlowupNormalBundle ↦ tangentialDivergence F z.1 z.2)
      (ν : Measure BlowupNormalBundle) :=
    BoundedContinuousFunction.integrable _ (blowupTangentTest hf hs)
  have hw := integrable_euclideanRadialWeight ν a r ε
  have hsl := integrable_euclideanRadialSlope ν a r ε
  have hbound := integral_mono (hw.const_mul 2) (ht.add (hsl.const_mul (2*r^2)))
    (fun z : BlowupNormalBundle ↦ radialDensityField_dilation_bound z.2.property a z.1 hr.le hε)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul,integral_add ht (hsl.const_mul _),integral_const_mul,hid] at hbound
  rw [(hasDerivAt_euclideanRadialMass ν a hε r).deriv,integral_const_mul]
  change 2 * euclideanRadialMass ν a ε r ≤ _ at hbound
  nlinarith

lemma euclideanRadialMass_tendsto (ν : FiniteMeasure BlowupNormalBundle) (a : Cover)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ euclideanRadialMass ν a ε r) (𝓝[>] 0) (𝓝 (euclideanBallMass ν a r)) := by
  have hm (ε : ℝ) := (integrable_euclideanRadialWeight ν a r ε).aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), ‖radialDensityWeight a r ε z.1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : BlowupNormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const _)
    (Eventually.of_forall fun z : BlowupNormalBundle ↦ radialDensityWeight_tendsto a z.1 hr)
  have he : (fun z : BlowupNormalBundle ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) z.1) =
      {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r}.indicator 1 := by
    ext z
    by_cases hz : z.1 ∈ Metric.ball a r
    · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r} from hz)]; rfl
    · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r} from hz)]
  rw [he,integral_indicator_one (s := {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r})
    (Metric.isOpen_ball.measurableSet.preimage measurable_fst)] at ht
  simpa only [smul_eq_mul,mul_one,euclideanRadialMass,euclideanBallMass] using ht

theorem stationary_euclideanBallMass_monotone {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1) :
    MonotoneOn (fun r : ℝ ↦ euclideanBallMass ν a r/r^2) (Ioc 0 R) := by
  have hs (ε : ℝ) (hε : 0 < ε) : MonotoneOn (fun r : ℝ ↦ euclideanRadialMass ν a ε r/r^2) (Ioc 0 R) := by
    have ho (r : ℝ) (hr : r ∈ Ioc 0 R) :
        (2 - 0 * r) * euclideanRadialMass ν a ε r ≤ r * deriv (euclideanRadialMass ν a ε) r := by
      have hh := stationary_euclideanRadialMass_ode hstat a hr.1 hε
        ((Metric.closedBall_subset_closedBall hr.2).trans hc)
      simpa only [zero_mul,sub_zero] using hh
    have hh := cmcDensityRatio_monotoneOn (k := 0) (R := R)
      (m := euclideanRadialMass ν a ε) (d := fun r ↦ deriv (euclideanRadialMass ν a ε) r)
      (fun r _ ↦ (hasDerivAt_euclideanRadialMass ν a hε r).differentiableAt.hasDerivAt) ho
    simpa using hh
  intro r hr s hs' hrs
  have hlr := (euclideanRadialMass_tendsto ν a hr.1).div_const (r^2)
  have hls := (euclideanRadialMass_tendsto ν a hs'.1).div_const (s^2)
  apply le_of_tendsto_of_tendsto hlr hls
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hs ε hε hr hs' hrs

theorem stationary_euclideanBallMass_density {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto (fun r : ℝ ↦ euclideanBallMass ν a r/r^2) (𝓝[>] 0) (𝓝 θ) := by
  apply exists_density_of_cmc_monotone (m := euclideanBallMass ν a) (k := 0) hR (fun _ _ ↦ ENNReal.toReal_nonneg)
  simpa using stationary_euclideanBallMass_monotone hstat a hc

lemma stationary_euclideanBallMass_upper {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    euclideanBallMass ν a r ≤ (euclideanBallMass ν a R/R^2)*r^2 := by
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mp
    (stationary_euclideanBallMass_monotone hstat a hc ⟨hr,hrR⟩ ⟨hR,le_rfl⟩ hrR)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_euclideanNormalMap (c : Cover) (r : ℝ) :
    Continuous (euclideanNormalMap c r) := by
  have hx : Continuous (fun z : BlowupNormalBundle ↦ (z.1 : Cover)) :=
    continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

lemma euclideanNormalMeasure_mass (μ : FiniteMeasure BlowupNormalBundle) (c : Cover) (r R : ℝ) :
    ((euclideanNormalMeasure μ c r R).mass : ℝ) = r⁻¹^2*euclideanBallMass μ c (r*R) := by
  change (((Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (euclideanNormalMap c r)) univ) : ℝ) = _
  rw [FiniteMeasure.smul_apply,FiniteMeasure.map_apply _
    (continuous_euclideanNormalMap c r).measurable MeasurableSet.univ]
  rw [Set.preimage_univ,FiniteMeasure.restrict_apply _ _ MeasurableSet.univ,univ_inter]
  change (Real.toNNReal (r⁻¹^2) : ℝ) *
    (((μ : Measure BlowupNormalBundle) {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma euclideanNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : BlowupNormalBundle) :
    (euclideanNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [euclideanNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

lemma euclideanNormalMeasure_supported (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    euclideanNormalMeasure μ c r R ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 := by
  have hm : MeasurableSet ((Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere))ᶜ) :=
    (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ).compl
  have he : (euclideanNormalMap c r ⁻¹' ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ)) ∩
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨Metric.ball_subset_closedBall ((euclideanNormalMap_mem c hr R z).mpr hz.2),mem_univ _⟩
  unfold euclideanNormalMeasure
  rw [FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (continuous_euclideanNormalMap c r).measurable hm,
    FiniteMeasure.restrict_apply _ _ (hm.preimage (continuous_euclideanNormalMap c r).measurable),he]
  simp [FiniteMeasure.coeFn_def]

theorem euclideanNormalMeasure_cluster {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, euclideanBallMass μ c (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ euclideanNormalMeasure μ c (r i) R) := by
  have hm (i) : (euclideanNormalMeasure μ c (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,euclideanNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ euclideanNormalMeasure μ c (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,euclideanNormalMeasure_supported μ c (hr i) R⟩))
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

lemma integral_euclideanNormalMeasure (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    (r R : ℝ) {g : BlowupNormalBundle → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂(euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z in {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)},
        g (euclideanNormalMap c r z) ∂(μ : Measure BlowupNormalBundle) := by
  rw [euclideanNormalMeasure,FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure,
    FiniteMeasure.toMeasure_map,integral_map
      (continuous_euclideanNormalMap c r).measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  change (Real.toNNReal (r⁻¹^2) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma integral_euclidean_normal_test (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r R : ℝ} (hr : 0 < r) {g : BlowupNormalBundle → ℝ} (hg : Continuous g)
    (hzero : ∀ z, z.1 ∉ Metric.ball (0 : Cover) R → g z = 0) :
    (∫ z, g z ∂(euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z, g (euclideanNormalMap c r z) ∂(μ : Measure BlowupNormalBundle) := by
  rw [integral_euclideanNormalMeasure μ c r R hg]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero _ (by rwa [euclideanNormalMap_mem c hr R z])

lemma stationary_euclidean_normal_identity {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (p : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall p r ⊆ Metric.closedBall (0 : Cover) 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(euclideanNormalMeasure ν p r R : Measure BlowupNormalBundle)) = 0 := by
  rw [integral_euclidean_normal_test ν p hr (continuous_blowupTangentTest hF)
    (fun z hz ↦ tangentialDivergence_zero_of_notMem_tsupport
      (fun h ↦ hz (Metric.closedBall_subset_ball hR (hs h))) z.2)]
  have hid := hstat (scaledTestField p r F) (scaledTestField_contDiff hF p r)
    ((scaledTestField_tsupport hs p hr).trans hc)
  simp only [tangentialDivergence_scaledTestField (hF.differentiable (by simp)) p _ _ hr.ne'] at hid
  change r⁻¹^2 * (∫ z, tangentialDivergence F (r⁻¹ • (z.1-p)) z.2 ∂(ν : Measure BlowupNormalBundle)) = 0
  rw [hid,mul_zero]

theorem stationary_euclidean_normal_limit {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {R : ℝ} (hR : 1 < R)
    {σ : FiniteMeasure BlowupNormalBundle}
    (hσ : Tendsto (fun i ↦ euclideanNormalMeasure ν p (r i) R) l (𝓝 σ))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hσ) (blowupTangentTest hF hFs)
  have he : (fun i ↦ ∫ z, tangentialDivergence F z.1 z.2 ∂(euclideanNormalMeasure ν p (r i) R : Measure BlowupNormalBundle)) =ᶠ[l] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    apply stationary_euclidean_normal_identity hstat p (hr i) hR _ hF hs
    intro x hx
    have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 1)
  exact tendsto_nhds_unique hweak (tendsto_const_nhds.congr' he.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma euclidean_normal_scaled_flux {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall p r ⊆ Metric.closedBall (0 : Cover) 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(euclideanNormalMeasure ν p r R : Measure BlowupNormalBundle)) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)*divergence F x := by
  rw [integral_euclidean_normal_test ν p hr (continuous_blowupFluxTest hF.continuous)
    (fun z hz ↦ by
      have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
      simp [image_eq_zero_of_notMem_tsupport hn])]
  have hid := hflux (scaledTestField p r F) (scaledTestField_contDiff hF p r)
    ((scaledTestField_tsupport hs p hr).trans hc)
  simp only [scaledTestField,inner_smul_right,integral_const_mul] at hid
  have hscale := integral_cover_affine_scaling
    (fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) x*divergence (scaledTestField p r F) x) p hr
  have hdiv (x : Cover) : divergence (scaledTestField p r F) (r • x+p) = divergence F x := by
    rw [divergence_scaledTestField (hF.differentiable (by simp)) p _ hr.ne']
    simp [hr.ne']
  simp_rw [hdiv] at hscale
  have heq : (∫ x in A, divergence (scaledTestField p r F) x) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence (scaledTestField p r F) x := by
    simp only [← indicator_mul_left,one_mul,integral_indicator hA]
  rw [heq,hscale] at hid
  change r⁻¹^2 * (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • (z.1-p))⟫ ∂(ν : Measure BlowupNormalBundle)) = _
  calc
    _ = (r*(∫ z, ⟪(z.2 : Cover), F (r⁻¹ • (z.1-p))⟫ ∂(ν : Measure BlowupNormalBundle)))/r^3 := by field_simp
    _ = _ := by rw [hid]; field_simp

theorem euclidean_normal_limit_flux {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {R : ℝ} (hR : 1 < R)
    {σ : FiniteMeasure BlowupNormalBundle}
    (hσ : Tendsto (fun i ↦ euclideanNormalMeasure ν p (r i) R) l (𝓝 σ))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in B, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hσ) (blowupFluxTest hF.continuous hFs)
  have hstrong := local_indicator_pairing_tendsto hA hB p r hconv (continuous_divergence hF)
    ((divergence_tsupport_subset F).trans hs)
  have he : (fun i ↦ ∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(euclideanNormalMeasure ν p (r i) R : Measure BlowupNormalBundle)) =ᶠ[l]
      (fun i ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*divergence F x) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    apply euclidean_normal_scaled_flux hA hflux p (hr i) hR _ hF hs
    intro x hx
    have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 1)
  exact tendsto_nhds_unique (hweak.congr' he) hstrong

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarAngularChart
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

lemma euclideanNormalMeasure_ball (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r ρ R : ℝ} (hr : 0 < r) (hρ : ρ ≤ R) :
    (euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = r⁻¹^2*euclideanBallMass μ c (r*ρ) := by
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} :=
    Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have he : euclideanNormalMap c r ⁻¹' {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} ∩
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} =
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*ρ)} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,euclideanNormalMap_mem c hr ρ]
    exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hρ hr.le) hz⟩⟩
  unfold euclideanNormalMeasure
  rw [FiniteMeasure.toMeasure_smul]
  change ((_ : Measure BlowupNormalBundle) _).toReal = _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,FiniteMeasure.toMeasure_map,
    Measure.map_apply (continuous_euclideanNormalMap c r).measurable hm,
    FiniteMeasure.restrict_measure_eq,Measure.restrict_apply
      (hm.preimage (continuous_euclideanNormalMap c r).measurable),he]
  simp only [ENNReal.coe_toReal,Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma euclideanNormalMeasure_ball_tendsto {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ euclideanBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    Tendsto (fun i ↦ (euclideanNormalMeasure μ c (r i) R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ}) l (𝓝 (θ*ρ^2)) := by
  have ht : Tendsto (fun i ↦ r i*ρ) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const ρ,
      Eventually.of_forall fun i ↦ mul_pos (hr i) hρ⟩
  have hh := (hθ.comp ht).mul_const (ρ^2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [euclideanNormalMeasure_ball μ c (hr i) hρR]
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',hρ.ne']

theorem euclidean_normal_limit_ball_mass {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ euclideanBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {R : ℝ} {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ euclideanNormalMeasure μ c (r i) R) l (𝓝 ν))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2 := by
  apply le_antisymm
  · exact finiteMeasure_real_open_upper hν (Metric.isOpen_ball.preimage continuous_fst)
      (euclideanNormalMeasure_ball_tendsto c r hr hrlim hθ hρ hρR.le)
  · have hlow (s : ℝ) (hs : s ∈ Ioo 0 ρ) : θ*s^2 ≤
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} := by
      apply (finiteMeasure_real_closed_lower hν
        (Metric.isClosed_closedBall.preimage continuous_fst)
        (show {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) s} ⊆
          {z | z.1 ∈ Metric.closedBall (0 : Cover) s} from fun _ hz ↦ Metric.ball_subset_closedBall hz)
        (euclideanNormalMeasure_ball_tendsto c r hr hrlim hθ hs.1 (hs.2.trans hρR).le)).trans
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem stationary_pair_secondary_cone {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0)) :
    ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ B ↔ x ∈ B) := by
  let R : ℝ := (1-‖p‖)/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hc : Metric.closedBall p R ⊆ Metric.closedBall (0 : Cover) 1 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by dsimp [R] at hx'; linarith : ‖x‖ ≤ 1)
  obtain ⟨θ,hθ,hdensity⟩ := stationary_euclideanBallMass_density hstat p hR hc
  let K : ℝ := euclideanBallMass ν p R/R^2
  have hK : 0 ≤ K := div_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds (half_pos hR)))
  let q : ℕ → ℝ := fun i ↦ r (i+k)
  have hq (i) : 0 < q i := hr _
  have hqb (i) : q i*2 ≤ R := by have hh := hk (i+k) (by omega); dsimp [q]; linarith
  have hmass (i) : euclideanBallMass ν p (q i*2) ≤ (K*4)*(q i)^2 := by
    have hh := stationary_euclideanBallMass_upper hstat p hR hc
      (mul_pos (hq i) (by norm_num : (0 : ℝ) < 2)) (hqb i)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨σ,_,hsup,hcl⟩ := euclideanNormalMeasure_cluster p q hq (by positivity : 0 ≤ K*4) hmass
  obtain ⟨U,hU,hσ⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hqlim : Tendsto q (U : Filter ℕ) (𝓝 0) :=
    (hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hconv' : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (q i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        (U : Filter ℕ) (𝓝 0) := (hconv.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hm (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
      (σ : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) b} = θ*b^2 :=
    euclidean_normal_limit_ball_mass p q hq hqlim hdensity hσ hb (by linarith)
  have hσstat (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    stationary_euclidean_normal_limit hstat p hp q hq hqlim (by norm_num : (1 : ℝ) < 2) hσ hF hs
  have hσflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    euclidean_normal_limit_flux hA hB hflux p hp q hq hqlim (by norm_num : (1 : ℝ) < 2) hσ hconv' hF hs
  have hrad := stationary_quadraticMass_radial_tangent hθ hm hσstat
  intro t ht
  exact radial_flux_cone_ae hB (fun ψ hψ hs ↦ limit_set_radial_flux hσflux hrad hψ hs) ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_smul {n : Cover} (hn : ‖n‖ = 1)
    (c : ℝ) (z : ℝ × Plane) :
    normalColumnChart 0 n (c • z) = c • normalColumnChart 0 n z := by
  rw [normalColumnChart_apply 0 hn,normalColumnChart_apply 0 hn]
  simp only [zero_add,Prod.smul_fst,Prod.smul_snd,smul_add,smul_smul]
  rw [show normalPlaneEmbedding n (c • z.2) = c • normalPlaneEmbedding n z.2 from
    (normalPlaneLinearIsometry n).map_smul c z.2]
  rfl

theorem conical_product_planar_cone {B : Set Cover} {C : Set Plane}
    {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ B ↔ x ∈ B))
    {t : ℝ} (ht : 1 ≤ t) :
    ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have htle : t⁻¹ ≤ 1 := (inv_le_one₀ ht0).mpr ht
  have hqm : Measure.QuasiMeasurePreserving (fun z : ℝ × Plane ↦ t⁻¹ • z) volume volume := by
    convert QuasiMeasurePreserving.prodMap
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero ht0.ne'))
        (Measure.quasiMeasurePreserving_smul (volume : Measure Plane) (inv_ne_zero ht0.ne')) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hscale := hqm.ae hprod
  have hconechart := (normalColumnChart_measurePreserving 0 n).quasiMeasurePreserving.ae (hcone t ht)
  have hh : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (t⁻¹ • z.2 ∈ C ↔ z.2 ∈ C) := by
    filter_upwards [hprod,hscale,hconechart] with z hz hzs hc hzt hzy
    have hnorm : ‖t⁻¹ • z.2‖ < 1/16 := by
      rw [norm_smul,Real.norm_of_nonneg htinv]
      exact (mul_le_of_le_one_left (norm_nonneg _) htle).trans_lt hzy
    have habs : |t⁻¹ * z.1| < 1/16 := by
      rw [abs_mul,abs_of_nonneg htinv]
      exact (mul_le_of_le_one_left (abs_nonneg _) htle).trans_lt hzt
    have hb : normalColumnChart 0 n z ∈ Metric.ball (0 : Cover) 1 := by
      rw [Metric.mem_ball,dist_zero_right,normalColumnChart_apply 0 hn,zero_add]
      have hh := norm_add_le (normalPlaneEmbedding n z.2) (z.1 • n)
      rw [normalPlaneEmbedding_norm,norm_smul,Real.norm_eq_abs,hn,mul_one] at hh
      linarith
    have he := hzs habs hnorm
    rw [normalColumnChart_smul hn] at he
    exact he.symm.trans ((hc hb).trans (hz hzt hzy))
  have hsplit := Measure.ae_ae_of_ae_prod hh
  have hpos : (volume : Measure ℝ) (Ioo (-(1/16 : ℝ)) (1/16)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hsplit)
  filter_upwards [hs] with y hy hyb
  exact hy (abs_lt.mpr hsI) (by simpa only [Metric.mem_ball,dist_zero_right] using hyb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarAxialBump_support : tsupport (planarAxialBump : ℝ → ℝ) ⊆
    Icc (-(1/32 : ℝ)) (1/32) := by
  rw [planarAxialBump.tsupport_eq,Real.closedBall_eq_Icc]
  simp [planarAxialBump]

theorem planar_product_directional_bound {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {L : ℝ} (hL : 0 ≤ L)
    (hper : coverLocalPerimeter B (Metric.ball (0 : Cover) (1/8)) ≤ ENNReal.ofReal L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K := by
  let J : ℝ := ∫ t : ℝ, planarAxialBump t
  have hJ : 0 < J := planarAxialBump.integral_pos
  refine ⟨L/J,div_nonneg hL hJ.le,?_⟩
  have hbound (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hsφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32))
      (hbφ : ∀ y, |φ y| ≤ 1) (u : Plane) (hu : ‖u‖ = 1) :
      (∫ y in C, fderiv ℝ φ y u) ≤ L/J := by
    let F : Cover → Cover := fun z ↦ normalScalarTest 0 n planarAxialBump φ z • normalPlaneEmbedding n u
    have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
      (normalScalarTest_contDiff 0 n planarAxialBump.contDiff hφ).smul_const _
    have hFs : tsupport F ⊆ Metric.ball (0 : Cover) (1/8) := by
      have hh := normalScalarTest_tsupport_ball 0 hn (by norm_num : (0 : ℝ)<3/32)
        (χ := planarAxialBump) (φ := φ)
        (by convert planarAxialBump_support using 1; norm_num)
        (by convert hsφ using 1; norm_num)
      exact (tsupport_smul_subset_left (f := normalScalarTest 0 n planarAxialBump φ) (g := fun _ ↦ normalPlaneEmbedding n u)).trans (hh.trans (Metric.ball_subset_ball (by norm_num)))
    have hFb (x) : ‖F x‖ ≤ 1 := by
      rw [norm_smul, normalPlaneEmbedding_norm,hu,mul_one,Real.norm_eq_abs]
      change |planarAxialBump ⟪n,x-0⟫*φ (normalPlaneCoordinates n (x-0))| ≤ 1
      rw [abs_mul,abs_of_nonneg planarAxialBump.nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) planarAxialBump.le_one).trans (hbφ _)
    have hh := integral_divergence_le_coverLocalPerimeter hper hL hF
      ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (hFs.trans Metric.ball_subset_closedBall)) hFs hFb
    rw [planar_product_flux hB hC hn hprod planarAxialBump.contDiff hφ
      planarAxialBump_support hsφ] at hh
    exact (le_div_iff₀ hJ).mpr (by simpa only [mul_comm,J] using hh)
  intro φ hφ hs hb u hu
  apply abs_le.mpr
  refine ⟨?_,hbound φ hφ hs hb u hu⟩
  have hh := hbound (-φ) hφ.neg (by simpa only [tsupport_neg] using hs)
    (by simpa only [Pi.neg_apply,abs_neg] using hb) u hu
  simpa only [fderiv_neg,Pi.neg_apply,neg_apply,integral_neg,neg_le] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
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

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

lemma coverLocalPerimeter_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B)) :
    coverLocalPerimeter A O = coverLocalPerimeter B O := by
  unfold coverLocalPerimeter
  apply iSup_congr; intro F
  apply iSup_congr; intro _
  apply iSup_congr; intro _
  apply iSup_congr; intro hs
  apply iSup_congr; intro _
  rw [setIntegral_divergence_congr_local hA hB hAB hs]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurableSet_coverHalfspace (n : Cover) : MeasurableSet (coverHalfspace n) :=
  measurableSet_lt (by fun_prop) measurable_const

lemma halfspace_indicator_eq (n : Cover) :
    (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) = halfspaceIndicator n := rfl

lemma setIntegral_coverHalfspace_divergence {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, ⟪n,F (normalPlaneEmbedding n y)⟫ := by
  have hh := integral_halfspace_divergence 0 hn hF hs
  simp only [sub_zero,zero_add] at hh
  rw [← hh,← halfspace_indicator_eq]
  simp only [← indicator_mul_left,one_mul,integral_indicator (measurableSet_coverHalfspace n)]

lemma coverHalfspace_flux_le {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {b : ℝ} (hb : 0 ≤ b) (hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b)
    (hbound : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in coverHalfspace n, divergence F x) ≤ Real.pi*b^2 := by
  rw [setIntegral_coverHalfspace_divergence hn hF hs]
  have hc : Continuous (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hh := (normalColumnChart_plane_isometry 0 hn 0).continuous
    simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] at hh
    exact continuous_const.inner (hF.continuous.comp hh)
  have hsc : HasCompactSupport (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hss := hs.comp_isClosedEmbedding (normalColumnChart_plane_isometry 0 hn 0).isClosedEmbedding
    have hh := hss.comp_left (show ⟪n,(0 : Cover)⟫ = 0 by simp)
    simpa only [Function.comp_def,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] using hh
  have hi : Integrable (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := hc.integrable_of_hasCompactSupport hsc
  have hbint : Integrable ((Metric.closedBall (0 : Plane) b).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hh := integral_mono hi hbint (fun y ↦ ?_)
  · have hv : (volume : Measure Plane).real (Metric.closedBall 0 b) = Real.pi*b^2 := by
      simp only [Measure.real,EuclideanSpace.volume_closedBall_fin_two,ENNReal.toReal_mul,
        ENNReal.toReal_pow,ENNReal.toReal_ofReal hb,ENNReal.toReal_ofReal Real.pi_pos.le]
      ring
    rw [integral_indicator Metric.isClosed_closedBall.measurableSet,integral_const,
      smul_eq_mul,mul_one,measureReal_restrict_apply_univ,hv] at hh
    exact hh
  · by_cases hy : y ∈ Metric.closedBall (0 : Plane) b
    · rw [indicator_of_mem hy]
      exact (real_inner_le_norm _ _).trans (by rw [hn,one_mul]; exact hbound _)
    · rw [indicator_of_notMem hy]
      have hz : F (normalPlaneEmbedding n y) = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (by
        simpa only [Metric.mem_closedBall,dist_zero_right,normalPlaneEmbedding_norm] using hFb hh))
      simp [hz]

lemma coverLocalPerimeter_halfspace_le {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 ≤ b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) ≤
      ENNReal.ofReal (Real.pi*b^2) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro hbF
  apply iSup_le; intro hbound
  exact ENNReal.ofReal_le_ofReal (coverHalfspace_flux_le hn hF hs hb hbF hbound)

theorem coverLocalPerimeter_halfspace {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm (coverLocalPerimeter_halfspace_le hn hb.le)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (integral_radialDensityWeight_plane_tendsto n hb)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
  have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
  have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
    (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
      (radialDensityWeight_tsupport hb.le hε)
  have hbound (x : Cover) : ‖F x‖ ≤ 1 := by
    change ‖radialDensityWeight 0 b ε x • n‖ ≤ 1
    rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  have he : (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    rw [setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  dsimp only [Function.comp_apply]
  rw [← he]
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le hFb (le_iSup_of_le hbound le_rfl))))

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_transverse_inner {n : Cover} (hn : ‖n‖ = 1)
    (m : Plane) (z : ℝ × Plane) :
    ⟪normalPlaneEmbedding n m, normalColumnChart 0 n z⟫ = ⟪m,z.2⟫ := by
  rw [normalColumnChart_apply 0 hn,zero_add,inner_add_right,inner_smul_right,
    real_inner_comm n (normalPlaneEmbedding n m),normalPlaneEmbedding_inner hn,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map m z.2

theorem planar_halfspace_lift {B : Set Cover} {C : Set Plane} {n : Cover}
    (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {m : Plane} (hm : m ≠ 0)
    (hhalf : ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) (1/16) →
      (y ∈ C ↔ 0 < ⟪m,y⟫)) :
    ∃ N : Cover, N ≠ 0 ∧ ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) (1/16) → (x ∈ B ↔ 0 < ⟪N,x⟫) := by
  have hm0 : normalPlaneEmbedding n m ≠ 0 := by
    intro hz
    have hh := normalPlaneEmbedding_norm n m
    rw [hz,norm_zero] at hh
    exact hm (norm_eq_zero.mp hh.symm)
  refine ⟨normalPlaneEmbedding n m,hm0,?_⟩
  have hy : ∀ᵐ z : ℝ × Plane ∂volume,
      z.2 ∈ Metric.ball (0 : Plane) (1/16) → (z.2 ∈ C ↔ 0 < ⟪m,z.2⟫) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))).ae hhalf
  have ha : ∀ᵐ z : ℝ × Plane ∂volume,
      normalColumnChart 0 n z ∈ Metric.ball (0 : Cover) (1/16) →
        (normalColumnChart 0 n z ∈ B ↔ 0 < ⟪normalPlaneEmbedding n m, normalColumnChart 0 n z⟫) := by
    filter_upwards [hprod,hy] with z hz hy hb
    have hnorm : ‖normalColumnChart 0 n z‖ < 1/16 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hb
    have ht : |z.1| < 1/16 := by
      have hh := abs_real_inner_le_norm n (normalColumnChart 0 n z)
      rw [hn,one_mul] at hh
      have he := normalColumnChart_height 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    have hp : ‖z.2‖ < 1/16 := by
      have hh := (normalPlaneCoordinates_lipschitz n).norm_sub_le (normalColumnChart 0 n z) 0
      simp only [map_zero,sub_zero,NNReal.coe_one,one_mul] at hh
      have he := normalColumnChart_projection 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    rw [normalColumnChart_transverse_inner hn]
    exact (hz ht hp).trans (hy (by simpa only [Metric.mem_ball,dist_zero_right] using hp))
  simpa only [MeasurableEquiv.apply_symm_apply] using
    (normalColumnChart_measurePreserving 0 n).symm.quasiMeasurePreserving.ae ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowupNormal_inner_integrable (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) :
    Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) ν := by
  apply Integrable.of_bound (show AEStronglyMeasurable _ _ from
    (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable) 1
  exact ae_of_all _ fun z ↦ by
    simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n

lemma radial_normal_flux_tendsto (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ ↦ ∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫
      ∂(ν : Measure BlowupNormalBundle)) (𝓝[>] 0)
      (𝓝 (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
        ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : BlowupNormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall fun ε : ℝ ↦ (show Continuous (fun z : BlowupNormalBundle ↦
      radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫) from by
        exact ((radialDensityWeight_contDiff 0 b ε).continuous.comp continuous_fst).mul
          ((continuous_subtype_val.comp continuous_snd).inner continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun ε : ℝ ↦ ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦ by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
      exact (mul_le_mul (radialDensityWeight_le_one _ _ _ _)
        (show ‖⟪(z.2 : Cover),n⟫‖ ≤ 1 by
          simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (integrable_const 1)
    (ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦
      (radialDensityWeight_tendsto 0 z.1 hb).mul_const ⟪(z.2 : Cover),n⟫)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [← integral_indicator (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from
    Metric.isOpen_ball.measurableSet.preimage measurable_fst)]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    dsimp only
    by_cases hz : z.1 ∈ Metric.ball (0 : Cover) b
    · rw [Set.indicator_of_mem (show z ∈ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_mem hz,one_mul]
    · rw [Set.indicator_of_notMem (show z ∉ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_notMem hz,zero_mul]

lemma flat_set_limit_flux_on_ball {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
      ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = Real.pi*b^2 := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
    have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
    have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
      (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
        (radialDensityWeight_tsupport hb.le hε)
    have hh := hflux F hF (hFb.trans (Metric.closedBall_subset_closedBall hb1.le))
    simp only [F,inner_smul_right] at hh
    rw [hh,setIntegral_divergence_congr_local hA (measurableSet_coverHalfspace n) hAn
      (hFb.trans (Metric.closedBall_subset_ball hb1)),setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  exact tendsto_nhds_unique (radial_normal_flux_tendsto ν hn hb)
    ((integral_radialDensityWeight_plane_tendsto n hb).congr' (he.mono fun _ h ↦ h.symm))

theorem flat_set_limit_normal {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hm : (ν : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n := by
  let B : Set BlowupNormalBundle := {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)}
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have hi := (blowupNormal_inner_integrable ν hn).integrableOn (s := B)
  have he := flat_set_limit_flux_on_ball hA hn hAn hflux
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hz : (∫ z in B, 1-⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    rw [integral_sub (integrable_const 1) hi,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    change (ν : Measure BlowupNormalBundle).real B-_ = 0
    rw [hm,he,sub_self]
  have hnneg : ∀ z : BlowupNormalBundle, 0 ≤ 1-⟪(z.2 : Cover),n⟫ := by
    intro z
    have hh := real_inner_le_norm (z.2 : Cover) n
    rw [z.2.property,hn,one_mul] at hh
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hnneg)
    ((integrable_const 1).sub hi)).mp hz
  have hae' := (ae_restrict_iff' hB).mp hae
  filter_upwards [hae'] with z hz hzb
  have hh := hz hzb
  change 1-⟪(z.2 : Cover),n⟫ = 0 at hh
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hs : ‖(z.2 : Cover)-n‖^2 = 0 := by rw [norm_sub_sq_real,z.2.property,hn]; nlinarith
  exact sq_eq_zero_iff.mp hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem conical_halfspace_extend {B : Set Cover}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) 1 → (t⁻¹ • x ∈ B ↔ x ∈ B))
    {N : Cover} (hN : N ≠ 0)
    (hhalf : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) (1/16) →
      (x ∈ B ↔ 0 < ⟪N,x⟫)) :
    ∃ n : Cover, ‖n‖ = 1 ∧ ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) 1 → (x ∈ B ↔ x ∈ coverHalfspace n) := by
  let n : Cover := -(‖N‖⁻¹ • N)
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_neg,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg N)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hN)]
  refine ⟨n,hn,?_⟩
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Cover)
    (by norm_num : (32 : ℝ)⁻¹ ≠ 0)
  filter_upwards [hc 32 (by norm_num),hq.ae hhalf] with x hx hh hb
  have hxb : (32 : ℝ)⁻¹ • x ∈ Metric.ball (0 : Cover) (1/16) := by
    have hx : ‖x‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hb
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  have he := (hx hb).symm.trans (hh hxb)
  rw [inner_smul_right] at he
  have hi : (0 < (32 : ℝ)⁻¹ * ⟪N,x⟫) ↔ 0 < ⟪N,x⟫ := mul_pos_iff_of_pos_left (by norm_num)
  refine (he.trans hi).trans ?_
  change (0 < ⟪N,x⟫) ↔ ⟪-(‖N‖⁻¹ • N),x⟫ < 0
  rw [inner_neg_left,inner_smul_left,neg_lt_zero]
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hN))).symm

lemma coverLocalPerimeter_halfspace_ball {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm
  · exact (coverLocalPerimeter_mono _ Metric.ball_subset_closedBall).trans
      (coverLocalPerimeter_halfspace_le hn hb.le)
  · have ht : Tendsto (fun a : ℝ ↦ ENNReal.ofReal (Real.pi*a^2)) (𝓝[<] b)
        (𝓝 (ENNReal.ofReal (Real.pi*b^2))) := by
      exact (ENNReal.continuous_ofReal.comp
        (show Continuous (fun a : ℝ ↦ Real.pi*a^2) by fun_prop)).continuousAt.tendsto.mono_left inf_le_left
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with a ha ha0
    rw [← coverLocalPerimeter_halfspace hn ha0]
    exact coverLocalPerimeter_mono _ (Metric.closedBall_subset_ball ha)

lemma halfspace_model_perimeter_ball {B : Set Cover} (hB : MeasurableSet B)
    {n : Cover} (hn : ‖n‖ = 1)
    (hhalf : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ B ↔ x ∈ coverHalfspace n))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    coverLocalPerimeter B (Metric.ball (0 : Cover) a) = ENNReal.ofReal (Real.pi*a^2) := by
  have he : coverLocalPerimeter B (Metric.ball (0 : Cover) a) =
      coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) a) := by
    apply coverLocalPerimeter_congr_local hB (measurableSet_coverHalfspace n)
    filter_upwards [hhalf] with x hx hb
    exact hx (Metric.ball_subset_ball ha1.le hb)
  rw [he]
  exact coverLocalPerimeter_halfspace_ball hn ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_secondary_halfspace {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p δ))
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ (B : Set Cover) (φ : ℕ → ℕ) (N : Cover),
      MeasurableSet B ∧ StrictMono φ ∧ ‖N‖ = 1 ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ B ↔ x ∈ coverHalfspace N)) ∧
      ∃ σ : FiniteMeasure BlowupNormalBundle,
        (∀ᵐ z ∂(σ : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
          (z.2 : Cover) = N) ∧
        ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
          tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
          (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
          (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in B, divergence F x := by
  obtain ⟨B,hB,φ,hφ,hBc,c,q,hc,hq,hqlim,hactual⟩ :=
    actual_tangent_secondary_representation hV hE hmin r hr hrlim hA hconv p hp s hs hs1 hslim
  let c' : ℕ → MovingCenter.InteriorCenter := fun i ↦ ⟨c i,hc i⟩
  have hn : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]
  have hline := radial_cone_secondary_unit_line hA hB hcone p hp hp0
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop) hBc
  obtain ⟨D,hD,hprodD⟩ := line_invariant_local_product hB hn hline
  obtain ⟨C,hC,hprod⟩ := line_product_euclidean hD hprodD
  have hBc' := stationary_pair_secondary_cone hA hB
    (fun F hF hFs ↦ (hstationary F hF hFs).1)
    (fun F hF hFs ↦ (hstationary F hF hFs).2) p hp
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop)
    (by simpa only [add_comm] using hBc)
  have hCc (t : ℝ) (ht : 1 ≤ t) := conical_product_planar_cone hn hprod hBc' ht
  obtain ⟨M,hM,hper⟩ := isMinimizerAt_moving_limit_perimeter hV hE hmin
  obtain ⟨K,hK,hbv⟩ := planar_product_directional_bound hB hC hn hprod
    (mul_nonneg hM.le (sq_nonneg (1/8 : ℝ)))
    (hper c' q hq hqlim B hB 1 hactual (1/8) (by norm_num) (by norm_num) (by norm_num))
  obtain ⟨b,hb,hden⟩ := isMinimizerAt_secondary_two_sided_density hV hE hmin
  have hBden := hden r hr hrlim A hA hconv p hp hboundary
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop) B hB hBc
  obtain ⟨ν',k,U,hU,hν',hsup,hstat'⟩ :=
    isMinimizerAt_moving_paired_normal_limit hV hE hmin hμ hH c' q hq hqlim hB hactual
  have hactual' := (hactual.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hq' := (hqlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hFs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) := (hstat' F hF hFs).2
  have heq (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :=
    moving_blowup_perimeter_eq_normal_ball hV hE hmin hμ
      (fun i ↦ c' (i+k)) (fun i ↦ q (i+k)) (fun i ↦ hq _) hq' hB hactual' hν' hflux ha ha1
  have hcomp (D : Set Cover) (hD : MeasurableSet D) (a b : ℝ)
      (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hBD : B ∆ D ⊆ Metric.ball (0 : Cover) a) :=
    isMinimizerAt_moving_limit_comparison hV hE hmin c' q hq hqlim
      hB hD hactual ha hab hb1 hb1 hBD
  obtain ⟨m,hm,hhalf⟩ := minimizing_planar_product_halfplane hB hC hn hcomp hprod hCc
    hK hbv heq hflux hb hBden
  obtain ⟨N,hN,hNmodel⟩ := planar_halfspace_lift hn hprod hm hhalf
  obtain ⟨n,hn,hmodel⟩ := conical_halfspace_extend hBc' hN hNmodel
  have hmass : (ν' : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2 := by
    rw [Measure.real_def,← heq (1/2) (by norm_num) (by norm_num),
      halfspace_model_perimeter_ball hB hn hmodel (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
  exact ⟨B,φ,n,hB,hφ,hn,hBc,hmodel,ν',flat_set_limit_normal hB hn hmodel hmass hflux,hstat'⟩

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

lemma ae_closedBall_imp_of_ae_ball {P : Cover → Prop} {a : Cover} {r : ℝ}
    (h : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball a r → P x) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.closedBall a r → P x := by
  have hz : ∀ᵐ x ∂(volume : Measure Cover), x ∉ Metric.sphere a r := by
    rw [ae_iff]
    simpa only [not_not,Metric.sphere,dist_eq_norm,Set.mem_ofPred_eq] using Measure.addHaar_sphere (volume : Measure Cover) a r
  filter_upwards [h,hz] with x hx hxz hxc
  apply hx
  have hh : dist x a ≤ r := hxc
  have hn : dist x a ≠ r := hxz
  exact lt_of_le_of_ne hh hn

lemma localL1_limit_congr_ae_ball {g : ℕ → Cover → ℝ} {f F : Cover → ℝ}
    {R : ℝ} {l : Filter ℕ}
    (heq : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) R → f x = F x)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R, |g i x-f x|) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x|) l (𝓝 0) := by
  have hh := ae_closedBall_imp_of_ae_ball heq
  have he (i : ℕ) : (∫ x in Metric.closedBall (0 : Cover) R, |g i x-f x|) =
      ∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x| := by
    apply setIntegral_congr_ae Metric.isClosed_closedBall.measurableSet
    filter_upwards [hh] with x hx hxb
    rw [hx hxb]
  simpa only [he] using hconv

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

theorem actual_primary_offvertex_fixed_graphs_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {σ : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ t : ℝ, 0 < t → 0 < volume.real (A ∩ Metric.ball p t) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p t)) :
    ∃ (n : Cover) (s e C K ρ : ℝ), ‖n‖ = 1 ∧ 0 < s ∧ s ≤ 1 ∧
      0 < e ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ C*e ≤ 1/2 ∧
      ∀ᶠ i in atTop,
        ActualBoundaryGraph E (cubeCenter+r i • p) n (r i*s) ∧
        BoundaryNormalChart E (cubeCenter+r i • p) n ((r i*s)/272) e C K ρ := by
  classical
  obtain ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,hpack⟩ :=
    actual_primary_fixed_scale_packets hV hE hmin hcenter hμ hH
  let e := min (δ/2) (1/(4*C))
  have he : 0 < e := by dsimp [e]; positivity
  have heδ : e ≤ δ := (min_le_left _ _).trans (by linarith)
  have hCe : C*e ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (min_le_right (δ/2) (1/(4*C)))
    change e*(4*C) ≤ 1 at hh
    nlinarith
  let t : ℕ → ℝ := fun i ↦ ((i:ℝ)+1)⁻¹
  have ht : ∀ i, 0 < t i := by intro i; dsimp [t]; positivity
  have ht1 : ∀ i, t i ≤ 1 := by
    intro i
    dsimp [t]
    exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have htlim : Tendsto t atTop (𝓝 0) := by
    simpa only [t,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨B,φ,n,hB,hφ,hn,hBc,hhalf,_⟩ :=
    actual_secondary_halfspace hV hE hmin hμ hH r hr hrlim hA hconv hcone hstationary
      p hp hp0 hboundary t ht ht1 htlim
  obtain ⟨η,hη,hηpack⟩ := hpack n hn e he heδ
  have heq : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      B.indicator (fun _ ↦ (1:ℝ)) x=(coverHalfspace n).indicator (fun _ ↦ (1:ℝ)) x := by
    filter_upwards [hhalf] with x hx hxb
    change (if x ∈ B then (1:ℝ) else 0) = if x ∈ coverHalfspace n then 1 else 0
    rw [propext (hx hxb)]
  have hconvH := localL1_limit_congr_ae_ball heq hBc
  obtain ⟨i,hi⟩ := (hconvH.eventually (Iio_mem_nhds hη)).exists
  refine ⟨n,t (φ i),e,C,K,ρ,hn,ht _,ht1 _,he,hC,hK,hρ,hρs,hCe,?_⟩
  exact hηpack r hr hrlim A hA hconv p hp hboundary (t (φ i)) (ht _) (ht1 _) hi

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.actual_primary_offvertex_fixed_graphs_oai := @OAI.CubicTorus.actual_primary_offvertex_fixed_graphs_oai
