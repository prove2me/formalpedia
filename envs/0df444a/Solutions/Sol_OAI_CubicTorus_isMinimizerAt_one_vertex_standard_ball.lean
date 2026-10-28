-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:18:29.12427+00:00
-- url     : https://prove2.me/submissions/0a11af3b-19ae-421f-bf21-cc13cc575f98

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_full_jacobi_system
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_positive_position_spherical
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_spherical_standard_ball

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
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

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

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

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

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

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
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMeasure_frontier_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), quotientMap z.1 ∈ frontier E := by
  have hh : ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus), c ∈ frontier E := by
    filter_upwards [Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))] with c hc
    have hc' := spatialNormalMeasure_support_subset_boundary hE hμ hc
    rw [frontier_eq_closure_inter_closure]
    exact ⟨Measure.support_restrict_subset.trans inter_subset_left hc'.1,
      Measure.support_restrict_subset.trans inter_subset_left hc'.2⟩
  change ∀ᵐ c ∂Measure.map normalProjection (μ : Measure NormalBundle), c ∈ frontier E at hh
  exact (ae_map_iff normalProjection_continuous.measurable.aemeasurable
    (show MeasurableSet {c : Torus | c ∈ frontier E} from isClosed_frontier.measurableSet)).mp hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
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

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
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

lemma localRadialSquared_lt_iff (a : Torus) (x : Cover) {r : ℝ}
    (hr : 0 ≤ r) (hs : r≤1/4) :
    localRadialSquared a x < r^2 ↔ quotientMap x∈Metric.ball a r := by
  have he := periodic_representative (localRadialSquared_periodic a) x
  rw [← he]
  change quotientMap x∈sublevelRegion (localRadialSquared a) (r^2) ↔ _
  rw [sublevelRegion_localRadialSquared a hr hs]

theorem exists_periodic_local_cutoff (a : Torus) {U : Set Torus}
    (hU : IsOpen U) (ha : a∈U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧ (∀ x,φ x∈Icc 0 1) ∧
      (∃ W : Set Torus,IsOpen W ∧ a∈W ∧
        ∀ x,quotientMap x∈W → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min (ε/4) (1/8 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrsmall : 2*r≤1/4 := by dsimp [r]; linarith [min_le_right (ε/4) (1/8 : ℝ)]
  have hrε : 2*r<ε := by dsimp [r]; linarith [min_le_left (ε/4) (1/8 : ℝ)]
  let q := localRadialSquared a
  let φ : Cover → ℝ := fun x ↦ Real.smoothTransition ((r^2-q x)/(r^2/2))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := localRadialSquared_contDiff a
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const _)
  have hden : 0 < r^2/2 := by positivity
  refine ⟨φ,hφ,?_,?_,?_,?_⟩
  · intro m x
    simp only [φ,q,localRadialSquared_periodic]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · refine ⟨Metric.ball a (r/2),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro x hx
    have hxq : q x<(r/2)^2 := (localRadialSquared_lt_iff a x (by positivity) (by linarith)).mpr hx
    have hn : ∀ᶠ y in 𝓝 x,q y < r^2/2 := hq.continuous.continuousAt.eventually_lt_const (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  · intro x hx
    have hnot : quotientMap x∉Metric.ball a (2*r) := fun hh ↦ hx (hεU (Metric.ball_subset_ball hrε.le hh))
    have hxq : (2*r)^2≤q x := le_of_not_gt (fun hh ↦ hnot ((localRadialSquared_lt_iff a x (by positivity) hrsmall).mp hh))
    have hn : ∀ᶠ y in 𝓝 x,r^2<q y := hq.continuous.continuousAt.eventually_const_lt (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_normal_base {F : Cover → ℝ} (hF : Continuous F)
    (μ : FiniteMeasure NormalBundle) :
    Integrable (fun z : NormalBundle ↦ F z.1) (μ : Measure NormalBundle) :=
  (hF.comp normalEmbedding_continuous.fst).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

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

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection
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

lemma coordinateReflection_continuous (i : Fin 3) : Continuous (coordinateReflection i) :=
  (coordinateReflection_isometry i).continuous

lemma coordinateReflection_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateReflection i) torusVolume torusVolume := by
  have h (j : Fin 3) : MeasurePreserving
      (fun a : AddCircle (1 : ℝ) => if j=i then -a else a) volume volume := by
    by_cases hj : j=i
    · simpa only [ite_eq_left hj] using (Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ))))
    · simp only [ite_eq_right hj]
      constructor
      · exact measurable_id
      · exact Measure.map_id
  exact product_to_torus_measurePreserving.comp ((volume_preserving_pi h).comp torus_to_product_measurePreserving)

lemma quotientMap_coordinateReflection (i : Fin 3) (x : Cover) :
    quotientMap (coverCoordinateReflection i x)=coordinateReflection i (quotientMap x) := by
  ext j
  by_cases h : j=i <;> simp [quotientMap,h]

lemma coverCoordinateReflection_lattice (i : Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinateReflection i (latticeVector m)=latticeVector (fun j => if j=i then -m j else m j) := by
  ext j
  by_cases h : j=i <;> simp [latticeVector,h]

lemma coverCoordinateReflection_single (i j : Fin 3) :
    coverCoordinateReflection i (EuclideanSpace.single j 1)=
      (if j=i then (-1 : ℝ) else 1) • EuclideanSpace.single j 1 := by
  ext k
  by_cases h : j=i
  · subst j
    by_cases hk : k=i <;> simp [hk]
  · by_cases hk : k=j
    · subst k; simp [h]
    · by_cases hi : k=i <;> simp [h,hk,hi]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateReflectedField_contDiff (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinateReflectedField i F) :=
  (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff)

lemma coordinateReflectedField_periodic (i : Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinateReflectedField i F (x+latticeVector n)=coordinateReflectedField i F x := by
  intro n x
  simp only [coordinateReflectedField,map_add,coverCoordinateReflection_lattice,hp]

lemma coordinateReflectedField_admissible (i : Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinateReflectedField i F) := by
  refine ⟨coordinateReflectedField_contDiff i hF.1,coordinateReflectedField_periodic i hF.2.1,?_⟩
  intro x
  simpa only [coordinateReflectedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinateReflection i x)

lemma coordinateReflectedField_divergence (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinateReflectedField i F) x=divergence F (coverCoordinateReflection i x) := by
  have hd : HasFDerivAt (coordinateReflectedField i F)
      ((coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinateReflection i x)).comp
          (coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinateReflection_single,map_smul,
    coverCoordinateReflection_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases h : j=i <;> simp [h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinateReflection (i : Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateReflection i ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinateReflectedField i F) x := by
  have hm := (coordinateReflection_continuous i).measurable
  have hr := coordinateReflectedField_admissible i hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinateReflectedField i F) (representative (coordinateReflection i z))) := by
    funext z
    rw [coordinateReflectedField_divergence i hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinateReflection i (representative (coordinateReflection i z))),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_involutive]
  rw [he]
  exact (coordinateReflection_measurePreserving i).setIntegral_preimage_emb
    (coordinateReflectionEquiv i).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinateReflectedField i F) (representative z)) E

lemma perimeter_coordinateReflection_le (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinateReflection i hF hE]
  exact le_iSup_of_le (coordinateReflectedField i F)
    (le_iSup_of_le (coordinateReflectedField_admissible i hF) le_rfl)

lemma perimeter_coordinateReflection_measurable (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinateReflection_le i hE)
  have hh := perimeter_coordinateReflection_le i ((coordinateReflection_continuous i).measurable hE)
  have he : coordinateReflection i ⁻¹' (coordinateReflection i ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSine_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordinateSine i) :=
  (contDiff_const.mul (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).sin

lemma coordinateSine_periodic (i : Fin 3) :
    ∀ n x,coordinateSine i (x+latticeVector n)=coordinateSine i x := by
  intro n x
  unfold coordinateSine
  simp only [PiLp.add_apply,latticeVector]
  rw [show 2*Real.pi*(x i+(n i : ℝ))=2*Real.pi*x i+(n i : ℝ)*(2*Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceGraphBundleMeasure
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

lemma mem_coordinateHalf_quotient (i : Fin 3) (a : ℝ) (x : Cover) :
    quotientMap x∈coordinateHalf i a ↔ Real.sin (2*Real.pi*(x i-a))<0 := by
  let q : Cover → ℝ := fun y => coordinateSine i (y-a • EuclideanSpace.single i 1)
  have hp : ∀ n y,q (y+latticeVector n)=q y := by
    intro n y
    dsimp [q]
    rw [show y+latticeVector n-a • EuclideanSpace.single i 1=
      (y-a • EuclideanSpace.single i 1)+latticeVector n by abel,coordinateSine_periodic]
  have he := periodic_representative hp x
  simp only [q,coordinateSine,PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,
    smul_eq_mul,mul_one] at he
  change Real.sin (2*Real.pi*((representative (quotientMap x)) i-a))<0 ↔ _
  rw [he]

lemma coordinateHalf_zero (i : Fin 3) : coordinateHalf i 0=sublevelRegion (coordinateSine i) 0 := by
  ext z
  simp only [coordinateHalf,sublevelRegion,coordinateSine,sub_zero,mem_ofPred_eq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateHalf_open (i : Fin 3) : IsOpen (coordinateHalf i 0) := by
  rw [coordinateHalf_zero]
  change IsOpen {z : Torus | coordinateSine i (representative z)<0}
  exact isOpen_lt (continuous_periodic_descent (coordinateSine_contDiff i).continuous
    (coordinateSine_periodic i)) continuous_const

lemma coordinateReflection_preimage_half (i : Fin 3) :
    coordinateReflection i ⁻¹' coordinateHalf i 0=coordinateHalf i (1/2) := by
  ext z
  obtain ⟨x,rfl⟩ := quotientMap_surjective z
  simp only [mem_preimage]
  rw [← quotientMap_coordinateReflection,mem_coordinateHalf_quotient,mem_coordinateHalf_quotient]
  simp only [sub_zero,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [show 2*Real.pi*(x i-1/2)=2*Real.pi*x i-Real.pi by ring,Real.sin_sub_pi]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_NormalMeasureCoordinateReflection
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

lemma volumeSupport_local_mono {E F U : Set Torus} (hU : IsOpen U)
    (hEF : E∩U⊆F∩U) {a : Torus} (haU : a∈U) (haE : a∈volumeSupport E) :
    a∈volumeSupport F := by
  have hh := Measure.interior_inter_support (μ := torusVolume.restrict E) (s := U)
  rw [hU.interior_eq] at hh
  have hh' := hh ⟨haU,haE⟩
  have he : (torusVolume.restrict E).restrict U=torusVolume.restrict (E∩U) := by
    rw [Measure.restrict_restrict hU.measurableSet,inter_comm]
  rw [he] at hh'
  exact (Measure.support_mono (Measure.restrict_mono (hEF.trans inter_subset_left) le_rfl)) hh'

lemma volumeSupport_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    volumeSupport E∩U=volumeSupport F∩U := by
  ext a
  constructor
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.subset ha.2 ha.1,ha.2⟩
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.symm.subset ha.2 ha.1,ha.2⟩

lemma isMinimizerAt_frontier_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U) :
    frontier (openRepresentative E)∩U=frontier (openRepresentative F)∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp he a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hh := volumeSupport_local_eq hU he
  have hc := volumeSupport_local_eq hU hec
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmE,
    isMinimizerAt_frontier_openRepresentative hW hF hmF]
  ext a
  have hh' := Set.ext_iff.mp hh a
  have hc' := Set.ext_iff.mp hc a
  simp only [mem_inter_iff] at *
  tauto

lemma local_region_flux_eq {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (he : E∩U=F∩U) {X : Cover → Cover}
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,X y=0) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence X x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,divergence X x := by
  classical
  rw [← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)),
    ← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hF))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : quotientMap x∈U
  · have hh := Set.ext_iff.mp he (quotientMap x)
    simp only [mem_inter_iff,hx,and_true] at hh
    simp only [Set.indicator_apply,mem_inter_iff,mem_preimage,hh]
  · have he0 : X=ᶠ[𝓝 x] (fun _ => 0) := hz x hx
    have hd : divergence X x=0 := by
      have hd0 : fderiv ℝ X x=0 := he0.fderiv_eq.trans (congrFun (fderiv_const (𝕜 := ℝ) (E := Cover) (c := (0 : Cover))) x)
      simp only [divergence,hd0,zero_apply,PiLp.zero_apply,Finset.sum_const_zero]
    simp only [Set.indicator_apply,hd,ite_self]

lemma local_region_weightedPerimeter_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {φ : Cover → ℝ} (hzero : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    weightedPerimeter E φ=weightedPerimeter F φ := by
  unfold weightedPerimeter
  congr 1
  funext X
  congr 1
  funext hX
  rw [local_region_flux_eq hE hF he (X := fun y => φ y • X y) (by
    intro x hx
    filter_upwards [hzero x hx] with y hy
    rw [hy,zero_smul])]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_region_weighted_mass_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ m x,φ (x+latticeVector m)=φ x) (hn : ∀ x,0≤φ x)
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
  have hh := local_region_weightedPerimeter_eq hE hF he hz
  rw [normalMeasure_weightedPerimeter hμ hφ hp hn,
    normalMeasure_weightedPerimeter hν hφ hp hn] at hh
  have hh' := congrArg ENNReal.toReal hh
  have hm0 : 0≤∫ z,φ z.1 ∂(μ : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  have hn0 : 0≤∫ z,φ z.1 ∂(ν : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  simpa only [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal hn0] using hh'

theorem isMinimizerAt_normal_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  obtain ⟨φ,hφ,hp,hb,⟨T,hT,hxT,hone⟩,hzero⟩ := exists_periodic_local_cutoff (quotientMap x) hU hx.2
  have hbound := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hxF : quotientMap x∈frontier (openRepresentative F) := (hbound ▸ hx).1
  have hunit (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E)) : ‖N y‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hpN]) (fun _ _ => rfl) _ y hy
    filter_upwards [haN] with z hz
    rw [hz,z.2.property]
  have hmass := local_region_weighted_mass_eq hE hF he hμ hν hφ hp (fun y => (hb y).1) hzero
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y • N y) := hφ.smul hN
  have hXp : ∀ k y,φ (y+latticeVector k) • N (y+latticeVector k)=φ y • N y :=
    fun k y => by rw [hp,hpN]
  have hflux : (∫ z,φ z.1*⟪(z.2 : Cover),N z.1⟫ ∂(ν : Measure NormalBundle))=
      ∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
    calc
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(ν : Measure NormalBundle) := by simp only [real_inner_smul_right]
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' F,divergence (fun y => φ y • N y) y := periodic_normal_flux hν hX hXp
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' E,divergence (fun y => φ y • N y) y :=
        (local_region_flux_eq hE hF he (by intro y hy; filter_upwards [hzero y hy] with z hz; rw [hz,zero_smul])).symm
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(μ : Measure NormalBundle) := (periodic_normal_flux hμ hX hXp).symm
      _ = ∫ z,φ z.1 ∂(μ : Measure NormalBundle) := by
        apply integral_congr_ae
        filter_upwards [haN] with z hz
        rw [real_inner_smul_right,hz,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
      _ = _ := hmass
  have hbF := normalMeasure_frontier_ae (E := openRepresentative F) (isOpen_openRepresentative F).measurableSet
    (hν.congr_ae (isMinimizerAt_openRepresentative_ae hW hF hmF).symm)
  have hid : (fun z : NormalBundle => φ z.1*‖N z.1-M z.1‖^2) =ᵐ[(ν : Measure NormalBundle)]
      (fun z => 2*(φ z.1-φ z.1*⟪(z.2 : Cover),N z.1⟫)) := by
    filter_upwards [haM,hbF] with z hz hzF
    by_cases hp0 : φ z.1=0
    · simp only [hp0,zero_mul,sub_self,mul_zero]
    · have hzU : quotientMap z.1∈U := by
        by_contra hh
        exact hp0 (hzero z.1 hh).self_of_nhds
      have hzE : quotientMap z.1∈frontier (openRepresentative E) := (hbound.symm.subset ⟨hzF,hzU⟩).1
      rw [hz,norm_sub_sq_real,hunit z.1 hzE,z.2.property,real_inner_comm]
      ring
  have hiφ := integrable_normal_base hφ.continuous ν
  have hiX : Integrable (fun z : NormalBundle => φ z.1*⟪(z.2 : Cover),N z.1⟫) (ν : Measure NormalBundle) := by
    simpa only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right] using
      (normalTest _ hX.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integrable_normal_base
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) ν
  have hiz : (∫ z,φ z.1*‖N z.1-M z.1‖^2 ∂(ν : Measure NormalBundle))=0 := by
    rw [integral_congr_ae hid,integral_const_mul,integral_sub hiφ hiX,hflux,sub_self,mul_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle =>
    mul_nonneg (hb z.1).1 (sq_nonneg _)) hi).mp hiz
  have hxzero := isMinimizerAt_periodic_ae_eq_boundary hW hF hmF hν
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) continuous_const
    (fun k y => by
      change φ (y+latticeVector k)*‖N (y+latticeVector k)-M (y+latticeVector k)‖^2=φ y*‖N y-M y‖^2
      rw [hp,hpN,hpM]) (fun _ _ => rfl) hae x hxF
  change φ x*‖N x-M x‖^2=0 at hxzero
  rw [(hone x hxT).self_of_nhds,one_mul] at hxzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hxzero))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_replace_ae {E F U : Set Torus} (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    ((F\U)∪(E∩U) : Set Torus) =ᵐ[torusVolume] F := by
  filter_upwards [he] with a ha
  have hh : (a∈E ∧ a∈U) ↔ (a∈F ∧ a∈U) := Iff.of_eq ha
  change (a∈(F\U)∪(E∩U))=(a∈F)
  apply propext
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma local_replace_inter (E F U : Set Torus) : ((F\U)∪(E∩U))∩U=E∩U := by
  ext a
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma isMinimizerAt_normal_local_ae_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  let F' := (F\U)∪(E∩U)
  have hF' : MeasurableSet F' := (hF.diff hU.measurableSet).union (hE.inter hU.measurableSet)
  have hrep : F' =ᵐ[torusVolume] F := local_replace_ae he
  exact isMinimizerAt_normal_local_eq hV hW hE hF' hmE ((isMinimizerAt_congr_ae hrep).mpr hmF)
    hU (local_replace_inter E F U).symm hμ (hν.congr_ae hrep.symm) hN hM hpN hpM haN haM x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_reflectNormal (i : Fin 3) : Measurable (reflectNormal i) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((coordinateReflection_continuous i).measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinateReflection i).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma reflectNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (i : Fin 3) (z : NormalBundle) :
    F (reflectNormal i z).1=F (coverCoordinateReflection i z.1) := by
  change F (representative (coordinateReflection i (quotientMap z.1)))=_
  rw [← quotientMap_coordinateReflection]
  exact periodic_representative hp _

lemma coverCoordinateReflection_inner (i : Fin 3) (x y : Cover) :
    ⟪coverCoordinateReflection i x,y⟫=⟪x,coverCoordinateReflection i y⟫ := by
  rw [← (coverCoordinateReflection i).inner_map_map x (coverCoordinateReflection i y),
    coverCoordinateReflection_involutive]

theorem isNormalMeasure_coordinateReflection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3) :
    IsNormalMeasure (coordinateReflection i ⁻¹' E) (μ.map (reflectNormal i)) := by
  constructor
  · have hm : ((μ.map (reflectNormal i)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_reflectNormal i)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_coordinateReflection_measurable i hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_reflectNormal i).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinateReflection i hF hE,← hμ.2 _ (coordinateReflectedField_admissible i hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinateReflection i z.2,F (reflectNormal i z).1⟫=
        ⟪(z.2 : Cover),coverCoordinateReflection i (F (coverCoordinateReflection i z.1))⟫
      rw [reflectNormal_periodic_eval hF.2.1,coverCoordinateReflection_inner]

lemma reflected_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    ∀ᵐ z ∂(μ.map (reflectNormal i) : Measure NormalBundle),
      coordinateReflectedField i N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_reflectNormal i).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinateReflection i).continuous.comp (hN.comp (coverCoordinateReflection i).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change coordinateReflectedField i N (reflectNormal i z).1=((reflectNormal i z).2 : Cover)
  rw [reflectNormal_periodic_eval (coordinateReflectedField_periodic i hp)]
  change coverCoordinateReflection i (N (coverCoordinateReflection i (coverCoordinateReflection i z.1)))=_
  rw [coverCoordinateReflection_involutive,hz]
  rfl

theorem isMinimizerAt_normal_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N x=coverCoordinateReflection i (N (coverCoordinateReflection i x)) := by
  have hmR := (isMinimizerAt_congr_ae hs).mpr hmE
  have hh : (E∩univ : Set Torus) =ᵐ[torusVolume] ((coordinateReflection i ⁻¹' E)∩univ : Set Torus) := by
    simpa only [inter_univ] using hs.symm
  exact isMinimizerAt_normal_local_ae_eq hV hV hE ((coordinateReflection_continuous i).measurable hE)
    hmE hmR isOpen_univ hh hμ (isNormalMeasure_coordinateReflection hE hμ i)
    hN (coordinateReflectedField_contDiff i hN) hp (coordinateReflectedField_periodic i hp)
    hae (reflected_normal_ae hN.continuous hp hae i) x ⟨hx,mem_univ _⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_NodalBalanceValue
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

lemma volumeSupport_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    volumeSupport (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (coordinateReflection i ⁻¹' E)∩Metric.ball a r=
      coordinateReflection i ⁻¹' (E∩Metric.ball (coordinateReflection i a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(coordinateReflection_isometry i).dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (coordinateReflection_measurePreserving i).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    openRepresentative (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinateReflection hE.compl]
  rfl

lemma frontier_openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    frontier (openRepresentative (coordinateReflection i ⁻¹' E))=
      coordinateReflection i ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinateReflection hE i]
  exact (coordinateReflectionEquiv i).toHomeomorph.preimage_frontier _ |>.symm

lemma frontier_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' frontier (openRepresentative E)=frontier (openRepresentative E) := by
  rw [← frontier_openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateChamber
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

lemma normalMeasure_test_translation_nonneg {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) {a : Cover}
    (hpos : ∀ t∈Icc (0 : ℝ) 1,∀ᵐ z ∂(μ : Measure NormalBundle),
      0≤f (z.1+t • a)*⟪(z.2 : Cover),a⟫) :
    0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x+a)-f x := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x+s • a))
      (fderiv ℝ f (x+t • a) a) t := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,one_smul,zero_add] using
      (hd (x+t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1,fderiv ℝ f (x+t • a) a)=f (x+a)-f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x+t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M,_,hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1+z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1+z.2 • a) a)
      ((volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M*‖a‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ f (z.1+z.2 • a)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t∈Ioc (0 : ℝ) 1) :
      0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,fderiv ℝ f (x+t • a) a := by
    let g : Cover → ℝ := fun x => f (x+t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ m x,g (x+latticeVector m)=g x := by
      intro m x; dsimp [g]; rw [add_right_comm,hp]
    have heq := periodic_normal_flux hμ (hg.smul_const a) (fun m x => by rw [hgp])
    simp only [real_inner_smul_right,divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g,fderiv_comp_add_right] at heq
    rw [← heq]
    exact integral_nonneg_of_ae (hpos t ⟨ht.1.le,ht.2⟩)
  calc
    0≤∫ t in Ioc (0 : ℝ) 1,∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        fderiv ℝ f (x+t • a) a :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc ht)
    _ = _ := by rw [← integral_integral_swap hi]; simp_rw [hFTC]

theorem isMinimizerAt_monotone_translation_test {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) (hf0 : ∀ x,0≤f x)
    (hsupp : ∀ t∈Icc (0 : ℝ) 1,∀ x : Cover,f (x+t • a)≠0 → quotientMap x∈U) :
    0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x+a)-f x := by
  apply normalMeasure_test_translation_nonneg hμ hf hp
  intro t ht
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmE).symm)
  filter_upwards [hbd,hae] with z hz hNz
  by_cases hzero : f (z.1+t • a)=0
  · rw [hzero,zero_mul]
  · rw [← hNz]
    exact mul_nonneg (hf0 _) (hsg z.1 ⟨hz,hsupp t ht z.1 hzero⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_open_swept_neighborhood {U : Set Torus} (hU : IsOpen U)
    (y : Torus) (a : Cover)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    ∃ W : Set Torus,IsOpen W ∧ y∈W ∧ ∀ z∈W,∀ t∈Icc (0 : ℝ) 1,z-quotientMap (t • a)∈U := by
  let O : Set (Torus × ℝ) := {z | z.1-quotientMap (z.2 • a)∈U}
  have hO : IsOpen O := hU.preimage
    (continuous_fst.sub (continuous_quotientMap.comp (continuous_snd.smul continuous_const)))
  have hs : ({y} : Set Torus) ×ˢ Icc (0 : ℝ) 1 ⊆ O := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    rw [mem_singleton_iff] at hz
    change z=y at hz
    subst z
    exact hpath t ht
  obtain ⟨W,J,hW,hJ,hy,hI,hsub⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hO hs
  exact ⟨W,hW,hy (mem_singleton y),fun z hz t ht => show (z,t)∈O from hsub ⟨hz,hI ht⟩⟩

theorem isMinimizerAt_no_reverse_crossing {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus} (hU : IsOpen U)
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {y : Torus} (hy : y∈openRepresentative E)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    y-quotientMap a∈closure (openRepresentative E) := by
  by_contra hx
  let F := openRepresentative E
  have hF : IsOpen F := isOpen_openRepresentative E
  have heF : F =ᵐ[torusVolume] E := isMinimizerAt_openRepresentative_ae hV hE hmE
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae heF).mpr hmE
  have hμF : IsNormalMeasure F μ := hμ.congr_ae heF.symm
  obtain ⟨W,hW,hyW,hWs⟩ := exists_open_swept_neighborhood hU y a hpath
  let O := W∩F∩(fun z : Torus => z-quotientMap a) ⁻¹' (closure F)ᶜ
  have hO : IsOpen O := (hW.inter hF).inter
    (isClosed_closure.isOpen_compl.preimage (continuous_id.sub continuous_const))
  have hyO : y∈O := ⟨⟨hyW,hy⟩,hx⟩
  obtain ⟨f,hf,hp,hb,⟨T,hT,hyT,hone⟩,hzero⟩ := exists_periodic_local_cutoff y hO hyO
  have hsupp : ∀ t∈Icc (0 : ℝ) 1,∀ x : Cover,f (x+t • a)≠0 → quotientMap x∈U := by
    intro t ht x hx
    have hqx : quotientMap (x+t • a)∈O := by
      by_contra hn
      exact hx ((hzero _ hn).self_of_nhds)
    have hh := hWs _ hqx.1.1 t ht
    simpa only [quotientMap_add,add_sub_cancel_right] using hh
  have hflux := isMinimizerAt_monotone_translation_test hV hF.measurableSet hmF hμF hae
    (U := U) (by
      intro x hx
      rw [openRepresentative_congr_ae heF] at hx
      exact hsg x hx) hf hp (fun x => (hb x).1) hsupp
  let g : Torus → ℝ := fun z => f (representative z)
  have hg : Continuous g := continuous_periodic_descent hf.continuous hp
  have hgb (z : Torus) : |g z|≤1 := by
    rw [abs_of_nonneg (hb _).1]
    exact (hb _).2
  have heq : (∫ x in F,g (x+quotientMap a)-g x ∂torusVolume)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,f (x+a)-f x := by
    rw [setIntegral_lift_measurable (f := fun x : Torus => g (x+quotientMap a)-g x) (hg.measurable.comp (measurable_id.add_const _) |>.sub hg.measurable) hF.measurableSet]
    apply setIntegral_congr_fun (measurableSet_fundamentalCube.inter
      (hF.measurableSet.preimage measurable_quotientMap))
    intro x hx
    simp only [g,← quotientMap_add,periodic_representative hp]
  rw [← heq,integral_difference_test hF.measurableSet hg.measurable hgb] at hflux
  have hid (z : Torus) : (characteristic F (z-quotientMap a)-characteristic F z)*g z= -g z := by
    by_cases hz : g z=0
    · simp only [hz,mul_zero,neg_zero]
    have hzO : z∈O := by
      by_contra hn
      apply hz
      exact (hzero (representative z) (by rwa [quotientMap_representative])).self_of_nhds
    have hzF := hzO.1.2
    have hxF : z-quotientMap a∉F := fun h => hzO.2 (subset_closure h)
    simp only [characteristic,indicator_of_mem hzF,indicator_of_notMem hxF,zero_sub,neg_mul,one_mul]
  simp_rw [hid] at hflux
  rw [integral_neg] at hflux
  have hpos : 0<∫ z,g z ∂torusVolume := by
    apply integral_pos_of_integrable_nonneg_nonzero hg
      (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun z => (hb _).1) (x := y)
    have hy1 : g y=1 := (hone (representative y) (by rwa [quotientMap_representative])).self_of_nhds
    rw [hy1]
    norm_num
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_regular_openRepresentative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    interior (closure (openRepresentative E))=openRepresentative E := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmEc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmE
  have he : openRepresentative E=(closure (openRepresentative Eᶜ))ᶜ := by
    rw [isMinimizerAt_closure_openRepresentative hVc hE.compl hmEc]
    rfl
  rw [he,closure_compl,interior_compl]
  congr 1
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (isOpen_openRepresentative Eᶜ).subset_interior_closure

theorem isMinimizerAt_monotone_segment {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus} (hU : IsOpen U)
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {y : Torus} (hy : y∈openRepresentative E)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    y-quotientMap a∈openRepresentative E := by
  obtain ⟨W,hW,hyW,hWs⟩ := exists_open_swept_neighborhood hU y a hpath
  let S : Set Torus := (fun z => z-quotientMap a) '' (W∩openRepresentative E)
  have hS : IsOpen S := (Homeomorph.subRight (quotientMap a)).isOpenMap _
    (hW.inter (isOpen_openRepresentative E))
  have hs : S⊆closure (openRepresentative E) := by
    rintro _ ⟨z,⟨hz,hzE⟩,rfl⟩
    exact isMinimizerAt_no_reverse_crossing hV hE hmE hμ hae hU hsg hzE (hWs z hz)
  have hx : y-quotientMap a∈S := ⟨y,⟨hyW,hy⟩,rfl⟩
  have hi := interior_mono hs (show y-quotientMap a∈interior S by rwa [hS.interior_eq])
  rwa [isMinimizerAt_regular_openRepresentative hV hE hmE] at hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateChamber_open (s : Fin 3 → Bool) : IsOpen (coordinateChamber s) := by
  apply isOpen_iInter_of_finite
  intro i
  cases hs : s i
  · simp only [Bool.false_eq_true,ite_false]
    rw [← coordinateReflection_preimage_half]
    exact (coordinateHalf_open i).preimage (coordinateReflection_continuous i)
  · simpa only [hs,ite_true] using coordinateHalf_open i

lemma mem_chamber_of_coordinates (s : Fin 3 → Bool) {x : Cover}
    (hx : ∀ i,chamberCorner s i<x i ∧ x i < chamberCorner s i+1/2) :
    quotientMap x∈coordinateChamber s := by
  rw [coordinateChamber,mem_iInter]
  intro i
  rw [mem_coordinateHalf_quotient]
  have hh := hx i
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hh
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hh.2]
    · nlinarith [Real.pi_pos,hh.1]
  · simp only [chamberCorner,hs,ite_true] at hh
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hh.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hh.1])
    simpa only [Real.sin_sub_two_pi] using hr

theorem isMinimizerAt_chamber_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    {x y : Cover} (hx : ∀ i,chamberCorner s i<x i ∧ x i < chamberCorner s i+1/2)
    (hy : ∀ i,chamberCorner s i<y i ∧ y i < chamberCorner s i+1/2)
    (hxy : ∀ i,x i≤y i) (hyE : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E := by
  have hpos : ∀ z : Cover,quotientMap z∈frontier (openRepresentative E)∩coordinateChamber s → 0≤⟪N z,y-x⟫ := by
    intro z hz
    rw [PiLp.inner_apply]
    exact Finset.sum_nonneg fun i _ => by
      simp only [RCLike.inner_apply,conj_trivial,PiLp.sub_apply]
      exact mul_nonneg (sub_nonneg.mpr (hxy i)) (hsg z hz i)
  have hpath : ∀ t∈Icc (0 : ℝ) 1,quotientMap y-quotientMap (t • (y-x))∈coordinateChamber s := by
    intro t ht
    rw [← quotientMap_sub]
    apply mem_chamber_of_coordinates
    intro i
    simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    constructor
    · nlinarith [hx i,hy i,mul_nonneg ht.1 (sub_nonneg.mpr (hxy i)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hxy i))]
    · nlinarith [hx i,hy i,mul_nonneg ht.1 (sub_nonneg.mpr (hxy i)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hxy i))]
  have hh := isMinimizerAt_monotone_segment hV hE hmE hμ hae (coordinateChamber_open s) hpos hyE hpath
  simpa only [← quotientMap_sub,sub_sub_cancel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma closure_openHalfBox (c : Cover) : closure (openHalfBox c)=closedHalfBox c := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have ho : openHalfBox c=e ⁻¹' (univ.pi fun i => Ioo (c i) (c i+1/2)) := by
    ext x; change (∀ i,c i<x i ∧ x i < c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Ioo (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Ioo]
  have hc : closedHalfBox c=e ⁻¹' (univ.pi fun i => Icc (c i) (c i+1/2)) := by
    ext x; change (∀ i,c i≤x i ∧ x i ≤ c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Icc (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Icc]
  rw [ho,hc]
  rw [← e.preimage_closure,closure_pi_set]
  congr 1
  apply pi_congr rfl
  intro i _
  exact closure_Ioo (by linarith)

lemma halfBox_downset_closure {c : Cover} {F : Set Cover}
    (hdown : ∀ x∈openHalfBox c,∀ y∈F∩openHalfBox c,(∀ i,x i≤y i) → x∈F)
    {x y : Cover} (hx : x∈closedHalfBox c)
    (hy : y∈closure (F∩openHalfBox c)) (hxy : ∀ i,x i≤y i) : x∈closure F := by
  let g : Cover × ℝ → Cover := fun z => WithLp.toLp 2 (fun i =>
    min ((1-z.2)*x i+z.2*(c i+1/4)) (z.1 i))
  have hg : Continuous g := (PiLp.continuous_toLp _ _).comp (continuous_pi fun i =>
    (((continuous_const.sub continuous_snd).mul continuous_const).add
      (continuous_snd.mul continuous_const)).min ((PiLp.continuous_apply _ _ i).comp continuous_fst))
  have hy0 : (y,(0 : ℝ))∈closure ((F∩openHalfBox c) ×ˢ Ioo (0 : ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    exact ⟨hy,by norm_num⟩
  have himg : g '' ((F∩openHalfBox c) ×ˢ Ioo (0 : ℝ) 1)⊆F := by
    rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    apply hdown _ ?_ z hz
    · intro i
      change min _ (z i)≤z i
      exact min_le_right _ _
    · intro i
      change c i < min _ (z i) ∧ min _ (z i) < c i+1/2
      have hc : c i<(1-t)*x i+t*(c i+1/4) ∧
          (1-t)*x i+t*(c i+1/4) < c i+1/2 := by
        have ht0 : 0<t := ht.1
        have ht1 : t<1 := ht.2
        constructor
        · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hx i).1)]
        · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hx i).2)]
      exact ⟨lt_min hc.1 (hz.2 i).1,(min_le_right _ _).trans_lt (hz.2 i).2⟩
  have hh := closure_mono himg (mem_closure_image hg.continuousAt hy0)
  have he : g (y,0)=x := by
    ext i
    change min ((1-0)*x i+0*(c i+1/4)) (y i)=x i
    simpa only [sub_zero,one_mul,zero_mul,add_zero] using min_eq_left (hxy i)
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma foldCoordinate_apply (i : Fin 3) (d : ℝ) (upper : Bool) (x : Cover) (j : Fin 3) :
    foldCoordinate i d upper x j=if j=i then
      (if upper then d-|x i-d| else d+|x i-d|) else x j := by
  by_cases hj : j=i
  · subst j; simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply]
  · simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply,hj]

lemma foldCoordinate_continuous (i : Fin 3) (d : ℝ) (upper : Bool) :
    Continuous (foldCoordinate i d upper) := by
  cases upper <;> unfold foldCoordinate <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    fun_prop

lemma quotientMap_centered_reflection (i : Fin 3) {d : ℝ}
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (x+(2*d-2*x i) • EuclideanSpace.single i 1)=coordinateReflection i (quotientMap x) := by
  obtain ⟨k,hk⟩ := hd
  have he : x+(2*d-2*x i) • EuclideanSpace.single i 1=
      coverCoordinateReflection i x+latticeVector (Pi.single i k) := by
    ext j
    by_cases hj : j=i
    · subst j
      simp [PiLp.add_apply,PiLp.smul_apply,latticeVector]
      linarith
    · simp [PiLp.add_apply,PiLp.smul_apply,latticeVector,hj]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero,quotientMap_coordinateReflection]

lemma foldCoordinate_quotient_alternative (i : Fin 3) {d : ℝ} (upper : Bool)
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (foldCoordinate i d upper x)=quotientMap x ∨
    quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
  have hsame (h : (if upper then d-|x i-d| else d+|x i-d|)=x i) :
      quotientMap (foldCoordinate i d upper x)=quotientMap x := by
    simp only [foldCoordinate,h,sub_self,zero_smul,add_zero]
  have href (h : (if upper then d-|x i-d| else d+|x i-d|)-x i=2*d-2*x i) :
      quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
    simp only [foldCoordinate,h,quotientMap_centered_reflection i hd]
  cases upper
  · by_cases hx : 0≤x i-d
    · exact Or.inl (hsame (by simp only [Bool.false_eq_true,ite_false,abs_of_nonneg hx]; ring))
    · exact Or.inr (href (by simp only [Bool.false_eq_true,ite_false,abs_of_neg (lt_of_not_ge hx)]; ring))
  · by_cases hx : x i-d≤0
    · exact Or.inl (hsame (by simp only [ite_true,abs_of_nonpos hx]; ring))
    · exact Or.inr (href (by simp only [ite_true,abs_of_pos (lt_of_not_ge hx)]; ring))

lemma localFoldCoordinate_apply (s : Fin 3 → Bool) (y : Cover) (i j : Fin 3) (x : Cover) :
    localFoldCoordinate s y i x j=if j=i then
      (if y i=chamberCorner s i then chamberCorner s i+|x i-chamberCorner s i|
       else if y i=chamberCorner s i+1/2 then chamberCorner s i+1/2-|x i-(chamberCorner s i+1/2)| else x i)
      else x j := by
  unfold localFoldCoordinate
  split_ifs <;> simp_all only [foldCoordinate_apply,Bool.false_eq_true,ite_false,ite_true]

lemma localChamberFold_apply (s : Fin 3 → Bool) (y x : Cover) (i : Fin 3) :
    localChamberFold s y x i=
      if y i=chamberCorner s i then chamberCorner s i+|x i-chamberCorner s i|
      else if y i=chamberCorner s i+1/2 then chamberCorner s i+1/2-|x i-(chamberCorner s i+1/2)| else x i := by
  fin_cases i <;> simp [localChamberFold,localFoldCoordinate_apply]

lemma localFoldCoordinate_continuous (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) :
    Continuous (localFoldCoordinate s y i) := by
  unfold localFoldCoordinate
  split_ifs <;> first | exact foldCoordinate_continuous _ _ _ | exact continuous_id

lemma localChamberFold_continuous (s : Fin 3 → Bool) (y : Cover) : Continuous (localChamberFold s y) :=
  (localFoldCoordinate_continuous s y 2).comp
    ((localFoldCoordinate_continuous s y 1).comp (localFoldCoordinate_continuous s y 0))

lemma localChamberFold_fixed (s : Fin 3 → Bool) (y : Cover) : localChamberFold s y y=y := by
  ext i
  rw [localChamberFold_apply]
  split_ifs with h₁ h₂
  · rw [h₁,sub_self,abs_zero,add_zero]
  · rw [h₂,sub_self,abs_zero,sub_zero]
  · rfl

lemma localChamberFold_mem_eventually (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) :
    ∀ᶠ x in 𝓝 y,localChamberFold s y x∈closedHalfBox (chamberCorner s) := by
  change ∀ᶠ x in 𝓝 y,∀ i,chamberCorner s i≤localChamberFold s y x i ∧
    localChamberFold s y x i ≤ chamberCorner s i+1/2
  rw [Filter.eventually_all]
  intro i
  have hc : ContinuousAt (fun x => localChamberFold s y x i) y :=
    ((PiLp.continuous_apply _ _ i).comp (localChamberFold_continuous s y)).continuousAt
  by_cases hlo : y i=chamberCorner s i
  · have hh : localChamberFold s y y i < chamberCorner s i+1/2 := by rw [localChamberFold_fixed,hlo]; linarith
    filter_upwards [hc.eventually_lt continuous_const.continuousAt hh] with x hx
    refine ⟨?_,hx.le⟩
    rw [localChamberFold_apply,ite_eq_left hlo]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · by_cases hup : y i=chamberCorner s i+1/2
    · have hh : chamberCorner s i<localChamberFold s y y i := by rw [localChamberFold_fixed,hup]; linarith
      filter_upwards [continuous_const.continuousAt.eventually_lt hc hh] with x hx
      refine ⟨hx.le,?_⟩
      rw [localChamberFold_apply,ite_eq_right hlo,ite_eq_left hup]
      exact sub_le_self _ (abs_nonneg _)
    · have hh₁ : chamberCorner s i<localChamberFold s y y i := by
        rw [localChamberFold_fixed]; exact lt_of_le_of_ne (hy i).1 (Ne.symm hlo)
      have hh₂ : localChamberFold s y y i < chamberCorner s i+1/2 := by
        rw [localChamberFold_fixed]; exact lt_of_le_of_ne (hy i).2 hup
      filter_upwards [continuous_const.continuousAt.eventually_lt hc hh₁,
        hc.eventually_lt continuous_const.continuousAt hh₂] with x h₁ h₂
      exact ⟨h₁.le,h₂.le⟩

lemma localFoldCoordinate_preserves {F : Set Torus}
    (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) {x : Cover} (hx : quotientMap x∈F) :
    quotientMap (localFoldCoordinate s y i x)∈F := by
  have hbase : ∃ k : ℤ,2*chamberCorner s i=(k : ℝ) := by
    cases hs : s i
    · exact ⟨0,by simp [chamberCorner,hs]⟩
    · exact ⟨1,by simp [chamberCorner,hs]⟩
  have htop : ∃ k : ℤ,2*(chamberCorner s i+1/2)=(k : ℝ) := by
    obtain ⟨k,hk⟩ := hbase
    exact ⟨k+1,by push_cast; linarith⟩
  have hh {d : ℝ} (b : Bool) (hd : ∃ k : ℤ,2*d=(k : ℝ)) : quotientMap (foldCoordinate i d b x)∈F := by
    rcases foldCoordinate_quotient_alternative i b hd x with he|he
    · rwa [he]
    · rw [he]
      change quotientMap x∈coordinateReflection i ⁻¹' F
      rwa [hF i]
  unfold localFoldCoordinate
  split_ifs
  · exact hh false hbase
  · exact hh true htop
  · exact hx

lemma localChamberFold_preserves {F : Set Torus}
    (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y : Cover) {x : Cover} (hx : quotientMap x∈F) :
    quotientMap (localChamberFold s y x)∈F :=
  localFoldCoordinate_preserves hF s y 2
    (localFoldCoordinate_preserves hF s y 1 (localFoldCoordinate_preserves hF s y 0 hx))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_isOpenMap : IsOpenMap quotientMap := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro a ⟨x,hx,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r,hr,?_⟩
  rw [← quotientMap_image_ball]
  exact image_mono hball

lemma openRepresentative_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' openRepresentative E=openRepresentative E := by
  rw [← openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

lemma chamber_closure_from_interior {F : Set Torus} (hF : IsOpen F)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) {y : Cover} (hy : y∈closedHalfBox (chamberCorner s))
    (hyF : quotientMap y∈closure F) :
    y∈closure ((quotientMap ⁻¹' F)∩openHalfBox (chamberCorner s)) := by
  have hyl : y∈closure (quotientMap ⁻¹' F) := by
    rw [← quotientMap_isOpenMap.preimage_closure_eq_closure_preimage continuous_quotientMap]
    exact hyF
  have hfreq := (mem_closure_iff_frequently.mp hyl).and_eventually
    (localChamberFold_mem_eventually s hy)
  have hh : ∃ᶠ x in 𝓝 y,localChamberFold s y x∈
      closure ((quotientMap ⁻¹' F)∩openHalfBox (chamberCorner s)) := by
    apply hfreq.mono
    rintro x ⟨hx,hxc⟩
    apply (hF.preimage continuous_quotientMap).inter_closure
    exact ⟨localChamberFold_preserves hs s y hx,by rwa [closure_openHalfBox]⟩
  have ht : Tendsto (localChamberFold s y) (𝓝 y) (𝓝 y) := by
    have hc := (localChamberFold_continuous s y).continuousAt (x := y)
    change Tendsto (localChamberFold s y) (𝓝 y) (𝓝 (localChamberFold s y y)) at hc
    rwa [localChamberFold_fixed] at hc
  exact isClosed_closure.mem_of_frequently_of_tendsto hh ht

theorem isMinimizerAt_chamber_closed_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyE : quotientMap y∈closure (openRepresentative E)) :
    quotientMap x∈closure (openRepresentative E) := by
  have hy' := chamber_closure_from_interior (isOpen_openRepresentative E)
    (fun i => openRepresentative_reflection_invariant hE i (hs i)) s hy hyE
  have hx' := halfBox_downset_closure (fun z hz w hw hzw =>
    isMinimizerAt_chamber_downset hV hE hmE hμ hae hsg hz hw.2 hzw hw.1) hx hy' hxy
  exact continuous_quotientMap.closure_preimage_subset (openRepresentative E) hx'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localChamberFold_mem_iff {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y x : Cover) :
    quotientMap (localChamberFold s y x)∈F ↔ quotientMap x∈F := by
  constructor
  · intro hx
    by_contra hn
    have hsc : ∀ i : Fin 3,coordinateReflection i ⁻¹' Fᶜ=Fᶜ := by
      intro i; rw [preimage_compl,hs i]
    exact localChamberFold_preserves hsc s y hn hx
  · exact localChamberFold_preserves hs s y

lemma reflection_invariant_closure {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' closure F=closure F := by
  intro i
  change (coordinateReflectionEquiv i).toHomeomorph ⁻¹' closure F=closure F
  rw [(coordinateReflectionEquiv i).toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage
    (coordinateReflection_continuous i)]
  change closure (coordinateReflection i ⁻¹' F)=closure F
  rw [hs i]

lemma chamber_open_downset_of_closed {F : Set Torus} (hF : IsOpen F)
    (hr : interior (closure F)=F)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    {s : Fin 3 → Bool}
    (hd : ∀ {x y : Cover},x∈closedHalfBox (chamberCorner s) →
      y∈closedHalfBox (chamberCorner s) → (∀ i,x i≤y i) →
      quotientMap y∈closure F → quotientMap x∈closure F)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyF : quotientMap y∈F) : quotientMap x∈F := by
  let g : Cover → Cover := fun z => WithLp.toLp 2 (fun i => max (y i) (localChamberFold s x z i))
  have hg : Continuous g := (PiLp.continuous_toLp _ _).comp (continuous_pi fun i =>
    continuous_const.max ((PiLp.continuous_apply _ _ i).comp (localChamberFold_continuous s x)))
  have he : g x=y := by
    ext i
    change max (y i) (localChamberFold s x x i)=y i
    rw [localChamberFold_fixed,max_eq_left (hxy i)]
  have hgf : ∀ᶠ z in 𝓝 x,quotientMap (g z)∈F := by
    apply ((hF.preimage continuous_quotientMap).preimage hg).mem_nhds
    change quotientMap (g x)∈F
    rwa [he]
  have hh : ∀ᶠ z in 𝓝 x,quotientMap z∈closure F := by
    filter_upwards [hgf,localChamberFold_mem_eventually s hx] with z hz hzc
    have hgz : g z∈closedHalfBox (chamberCorner s) := by
      intro i
      exact ⟨(hy i).1.trans (le_max_left _ _),max_le (hy i).2 (hzc i).2⟩
    have horder : ∀ i,localChamberFold s x z i≤g z i := fun i => le_max_right _ _
    exact (localChamberFold_mem_iff (reflection_invariant_closure hs) s x z).mp
      (hd hzc hgz horder (subset_closure hz))
  have hi : x∈interior (quotientMap ⁻¹' closure F) := mem_interior_iff_mem_nhds.mpr hh
  have hqi := quotientMap_isOpenMap.interior_preimage_subset_preimage_interior hi
  change quotientMap x∈interior (closure F) at hqi
  rwa [hr] at hqi

theorem isMinimizerAt_chamber_open_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyE : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E :=
  chamber_open_downset_of_closed (isOpen_openRepresentative E)
    (isMinimizerAt_regular_openRepresentative hV hE hmE)
    (fun i => openRepresentative_reflection_invariant hE i (hs i))
    (fun hx hy hxy hyE => isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs hx hy hxy hyE)
    hx hy hxy hyE

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberGlobalFold
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

lemma abs_shortestLift_coordinate (a : Torus) (i : Fin 3) : |shortestLift a i|≤1/2 := by
  have hh := compactCell_coordinates (cubeRepresentative (a+quotientMap cubeCenter)) i
  change 0 ≤ representative (a+quotientMap cubeCenter) i ∧ representative (a+quotientMap cubeCenter) i≤1 at hh
  change |representative (a+quotientMap cubeCenter) i-1/2|≤1/2
  exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩

lemma chamberFoldLift_apply (s : Fin 3 → Bool) (a : Torus) (i : Fin 3) :
    chamberFoldLift s a i=chamberCorner s i+|shortestLift (a-quotientMap (chamberCorner s)) i| := by
  simp only [chamberFoldLift,localChamberFold_apply,ite_true,PiLp.add_apply,add_sub_cancel_right]

lemma chamberFoldLift_mem (s : Fin 3 → Bool) (a : Torus) :
    chamberFoldLift s a∈closedHalfBox (chamberCorner s) := by
  intro i
  rw [chamberFoldLift_apply]
  exact ⟨le_add_of_nonneg_right (abs_nonneg _),by linarith [abs_shortestLift_coordinate (a-quotientMap (chamberCorner s)) i]⟩

lemma chamberFoldLift_mem_iff {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) (s : Fin 3 → Bool) (a : Torus) :
    quotientMap (chamberFoldLift s a)∈F ↔ a∈F := by
  rw [chamberFoldLift,localChamberFold_mem_iff hs,quotientMap_add,quotientMap_shortestLift,sub_add_cancel]

lemma chamberVertex_mem (s b : Fin 3 → Bool) : chamberVertex s b∈closedHalfBox (chamberCorner s) := by
  intro i
  change chamberCorner s i ≤ chamberCorner s i+(if b i then 1/2 else 0) ∧
    chamberCorner s i+(if b i then 1/2 else 0) ≤ chamberCorner s i+1/2
  cases b i <;> norm_num

lemma chamberVertex_mono (s : Fin 3 → Bool) {b d : Fin 3 → Bool} (hbd : b≤d) :
    ∀ i,chamberVertex s b i ≤ chamberVertex s d i := by
  intro i
  have hh := hbd i
  cases hb : b i <;> cases hd : d i <;> simp_all [chamberVertex]
  exact ((by decide : ¬(true : Bool)≤false) hh).elim

lemma chamberVertex_bottom (s : Fin 3 → Bool) : chamberVertex s (fun _ => false)=chamberCorner s := by
  ext i; simp [chamberVertex]

lemma chamberVertex_bottom_le (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) : ∀ i,chamberVertex s (fun _ => false) i≤y i := by
  rw [chamberVertex_bottom]
  exact fun i => (hy i).1

lemma chamberVertex_le_top (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) : ∀ i,y i ≤ chamberVertex s (fun _ => true) i :=
  fun i => (hy i).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_openRepresentative_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    (openRepresentative E).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro he
  have hh := (measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmE)).trans hmE.2.1
  rw [he,measure_empty] at hh
  exact (ENNReal.ofReal_pos.mpr hV.1).ne' hh.symm

lemma isMinimizerAt_vacant_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    (closure (openRepresentative E))ᶜ.Nonempty := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmEc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmE
  have he : (closure (openRepresentative E))ᶜ=openRepresentative Eᶜ := by
    rw [isMinimizerAt_closure_openRepresentative hV hE hmE,openRepresentative,compl_compl]
  rw [he]
  exact isMinimizerAt_openRepresentative_nonempty hVc hE.compl hmEc

theorem isMinimizerAt_chamber_vertex_order {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    quotientMap (chamberVertex s (fun _ => false))∈openRepresentative E ∧
    quotientMap (chamberVertex s (fun _ => true))∉closure (openRepresentative E) ∧
    ∀ b d : Fin 3 → Bool,b≤d → quotientMap (chamberVertex s d)∈openRepresentative E →
      quotientMap (chamberVertex s b)∈openRepresentative E := by
  have hsF := fun i => openRepresentative_reflection_invariant hE i (hs i)
  constructor
  · obtain ⟨a,ha⟩ := isMinimizerAt_openRepresentative_nonempty hV hE hmE
    exact isMinimizerAt_chamber_open_downset hV hE hmE hμ hae hsg hs
      (chamberVertex_mem s _) (chamberFoldLift_mem s a)
      (chamberVertex_bottom_le s (chamberFoldLift_mem s a))
      ((chamberFoldLift_mem_iff hsF s a).mpr ha)
  constructor
  · intro htop
    obtain ⟨a,ha⟩ := isMinimizerAt_vacant_nonempty hV hE hmE
    have hfold := isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs
      (chamberFoldLift_mem s a) (chamberVertex_mem s _)
      (chamberVertex_le_top s (chamberFoldLift_mem s a)) htop
    exact ha ((chamberFoldLift_mem_iff (reflection_invariant_closure hsF) s a).mp hfold)
  · intro b d hbd hd
    exact isMinimizerAt_chamber_open_downset hV hE hmE hμ hae hsg hs
      (chamberVertex_mem s _) (chamberVertex_mem s _) (chamberVertex_mono s hbd) hd

theorem isMinimizerAt_vacant_face {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E))
    {x : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hxi : x i=chamberCorner s i+1/2) : quotientMap x∉closure (openRepresentative E) := by
  intro hxE
  apply hv
  apply isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs
    (chamberVertex_mem s _) hx ?_ hxE
  intro j
  by_cases hj : j=i
  · subst j
    change chamberCorner s i+(if decide (i=i) then 1/2 else 0)≤x i
    simp only [decide_true,ite_true,hxi]
    exact le_rfl
  · simpa [chamberVertex,hj] using (hx j).1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isCompact_closedHalfBox (c : Cover) : IsCompact (closedHalfBox c) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have he : closedHalfBox c=e ⁻¹' (univ.pi fun i => Icc (c i) (c i+1/2)) := by
    ext x
    change (∀ i,c i≤x i ∧ x i ≤ c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Icc (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Icc]
  rw [he]
  exact e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi fun _ => isCompact_Icc)

theorem isMinimizerAt_chamber_face_gap {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈closedHalfBox (chamberCorner s),
      quotientMap x∈closure (openRepresentative E) → x i ≤ chamberCorner s i+1/2-δ := by
  let K := closedHalfBox (chamberCorner s) ∩ quotientMap ⁻¹' closure (openRepresentative E)
  have hK : IsCompact K := (isCompact_closedHalfBox _).inter_right
    (isClosed_closure.preimage continuous_quotientMap)
  by_cases hn : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hn (PiLp.continuous_apply _ _ i).continuousOn
    have hlt : x i < chamberCorner s i+1/2 := lt_of_le_of_ne (hx.1 i).2 (by
      intro he
      exact isMinimizerAt_vacant_face hV hE hmE hμ hae hsg hs i hv hx.1 he hx.2)
    refine ⟨chamberCorner s i+1/2-x i,sub_pos.mpr hlt,?_⟩
    intro y hy hyE
    have hh := hmax ⟨hy,hyE⟩
    dsimp at hh
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro x hx hxE
    exact (hn ⟨x,hx,hxE⟩).elim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_coordinateHalf_of_chamber_interval (s : Fin 3 → Bool) (x : Cover) (i : Fin 3)
    (hx : chamberCorner s i<x i ∧ x i < chamberCorner s i+1/2) :
    quotientMap x∈coordinateHalf i (if s i then 0 else 1/2) := by
  rw [mem_coordinateHalf_quotient]
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hx
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hx.2]
    · nlinarith [Real.pi_pos,hx.1]
  · simp only [chamberCorner,hs,ite_true] at hx
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hr

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SliceJensenWeight
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

lemma chamber_corner_coordinate_twice (s : Fin 3 → Bool) (i : Fin 3) :
    2*chamberCorner s i = ((if s i then 1 else 0 : ℤ) : ℝ) := by
  cases hs : s i <;> norm_num [chamberCorner,hs]

lemma chamber_reflected_coordinate (s : Fin 3 → Bool) (i : Fin 3) (x : Cover) :
    (coverCoordinateReflection i x+latticeVector
      (fun j => if j=i then (if s i then 1 else 0 : ℤ) else 0)) i=
      2*chamberCorner s i-x i := by
  simp only [PiLp.add_apply,coverCoordinateReflection_apply,ite_true,latticeVector]
  rw [← chamber_corner_coordinate_twice]
  ring

theorem isMinimizerAt_chamber_support_positive {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (hbox : ∀ i : Fin 3,|x i-chamberCorner s i|<1/2)
    (hne : x≠chamberCorner s) : 0<⟪N x,x-chamberCorner s⟫ := by
  have hsign (i : Fin 3) : x i≠chamberCorner s i → 0<N x i*(x i-chamberCorner s i) := by
    intro hi
    rcases lt_or_gt_of_ne hi with hlt|hgt
    · let m : Fin 3 → ℤ := fun j => if j=i then (if s i then 1 else 0) else 0
      let y := coverCoordinateReflection i x+latticeVector m
      have hy : quotientMap y∈frontier (openRepresentative E) := by
        rw [show quotientMap y=coordinateReflection i (quotientMap x) by
          change quotientMap (coverCoordinateReflection i x+latticeVector m)=_
          rw [quotientMap_add,quotientMap_latticeVector,add_zero,quotientMap_coordinateReflection]]
        change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
        rwa [frontier_reflection_invariant hE i (hs i)]
      have hcoord : y i=2*chamberCorner s i-x i := chamber_reflected_coordinate s i x
      have hb := abs_lt.mp (hbox i)
      have hyhalf := mem_coordinateHalf_of_chamber_interval s y i
        (show chamberCorner s i<y i ∧ y i < chamberCorner s i+1/2 by
          rw [hcoord]; constructor <;> linarith [hb.1])
      have hNy := hsg y i ⟨hy,hyhalf⟩
      have hNr := congrArg (fun v : Cover => v i)
        (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
      simp only [coverCoordinateReflection_apply,ite_true] at hNr
      have hNp : N y i=N (coverCoordinateReflection i x) i := congrArg (fun v : Cover => v i) (hp m _)
      rw [hNp] at hNy
      apply mul_pos_of_neg_of_neg
      · linarith
      · exact sub_neg.mpr hlt
    · have hb := abs_lt.mp (hbox i)
      exact mul_pos (hsg x i ⟨hx,mem_coordinateHalf_of_chamber_interval s x i
        ⟨hgt,by linarith [hb.2]⟩⟩) (sub_pos.mpr hgt)
  have hex : ∃ i : Fin 3,x i≠chamberCorner s i := by
    by_contra hn
    push Not at hn
    exact hne (by ext i; exact hn i)
  obtain ⟨i,hi⟩ := hex
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,PiLp.sub_apply]
  apply Finset.sum_pos'
  · intro j _
    by_cases hj : x j=chamberCorner s j
    · simp [hj]
    · simpa only [mul_comm] using (hsign j hj).le
  · exact ⟨i,Finset.mem_univ i,by simpa only [mul_comm] using hsign i hi⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_periodic_position_box (c : Cover) {r : ℝ} (hr : 0 < r) (hr' : r<1/2) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      ∀ x : Cover,(∀ i : Fin 3,|x i-c i| ≤ r) →
        X=ᶠ[𝓝 x](fun y => y-c) := by
  let b : ContDiffBump (1/2 : ℝ) :=
    ⟨(r+1/2)/2,(r+3/2)/4,by positivity,by linarith⟩
  let χ : Cover → ℝ := fun x => ∏ i : Fin 3,b (x i)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_prod fun i _ =>
    b.contDiff.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  let g : Cover → Cover := fun x => χ x • (x-cubeCenter)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul (contDiff_id.sub contDiff_const)
  let K : Set Cover := {x | ∀ i : Fin 3,|x i-1/2|≤b.rOut}
  have hK : IsClosed K := by
    change IsClosed {x : Cover | ∀ i : Fin 3,|x i-1/2|≤b.rOut}
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.sub continuous_const).abs) continuous_const
  have hsK : tsupport g⊆K := by
    apply closure_minimal _ hK
    intro x hx i
    have hc : χ x≠0 := by
      intro hz
      exact hx (by simp only [g,hz,zero_smul])
    have hi : b (x i)≠0 := (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
    have hmem : x i∈tsupport (b : ℝ → ℝ) := subset_closure hi
    rw [b.tsupport_eq] at hmem
    simpa only [Metric.mem_closedBall,Real.dist_eq] using hmem
  have hsO : tsupport g⊆{x : Cover | ∀ i,0<x i ∧ x i<1} := by
    intro x hx i
    have hh := abs_le.mp (hsK hx i)
    change -((r+3/2)/4)≤x i-1/2 ∧ x i-1/2≤(r+3/2)/4 at hh
    constructor <;> linarith [hh.1,hh.2]
  have hcomp : HasCompactSupport g := isCompact_closedFundamentalCube.of_isClosed_subset isClosed_closure (by
    intro x hx
    refine ⟨WithLp.ofLp x,?_,by simp⟩
    exact ⟨fun i => (hsO hx i).1.le,fun i => (hsO hx i).2.le⟩)
  let P := latticePeriodize g
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := latticePeriodize_contDiff hg hcomp
  let X : Cover → Cover := fun x => P (x-c+cubeCenter)
  refine ⟨X,hP.comp ((contDiff_id.sub contDiff_const).add contDiff_const),?_,?_⟩
  · intro m x
    change P (x+latticeVector m-c+cubeCenter)=P (x-c+cubeCenter)
    rw [show x+latticeVector m-c+cubeCenter=(x-c+cubeCenter)+latticeVector m by abel]
    exact latticePeriodize_periodic g m _
  · intro x hx
    let y := x-c+cubeCenter
    have hy (i : Fin 3) : 0≤y i ∧ y i≤1 := by
      have hh := abs_le.mp (hx i)
      change 0≤x i-c i+1/2 ∧ x i-c i+1/2≤1
      constructor <;> linarith [hh.1,hh.2]
    have hb (i : Fin 3) : ∀ᶠ z in 𝓝 y,b (z i)=1 := by
      have hh : y i∈Metric.ball (1/2 : ℝ) b.rIn := by
        change |(x i-c i+1/2)-1/2|<(r+1/2)/2
        simp only [add_sub_cancel_right]
        exact (hx i).trans_lt (by linarith)
      exact (b.eventuallyEq_one_of_mem_ball hh).comp_tendsto
        (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.continuousAt
    have hb' : ∀ᶠ z in 𝓝 y,χ z=1 := by
      filter_upwards [Filter.eventually_all.mpr hb] with z hz
      dsimp [χ]
      simp_rw [hz]
      simp
    have he : P=ᶠ[𝓝 y](fun z => z-cubeCenter) := by
      filter_upwards [latticePeriodize_eventuallyEq hcomp hsO hy,hb'] with z hz hχz
      change latticePeriodize g z=_
      rw [hz]
      simp only [g,hχz,one_smul]
    have ht : Tendsto (fun z : Cover => z-c+cubeCenter) (𝓝 x) (𝓝 y) :=
      ((continuous_id.sub continuous_const).add continuous_const).continuousAt
    filter_upwards [he.comp_tendsto ht] with z hz
    simpa only [X,Function.comp_apply,add_sub_cancel_right] using hz

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberPositionProducer
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

theorem isMinimizerAt_one_vertex_position {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        fderiv ℝ X x=ContinuousLinearMap.id ℝ Cover ∧ 0<⟪N x,X x⟫ := by
  have hsgc : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i := by
    intro x hx i
    exact (hsg x i ⟨hx.1,mem_iInter.mp hx.2 i⟩).le
  have hgap := fun i => isMinimizerAt_chamber_face_gap hV hE hm hμ ha hsgc hs i (hv i)
  choose d hd hgap using hgap
  let δ := min (1/4 : ℝ) (min (d 0) (min (d 1) (d 2)))
  have hδ : 0<δ := lt_min (by norm_num) (lt_min (hd 0) (lt_min (hd 1) (hd 2)))
  have hδq : δ≤1/4 := min_le_left _ _
  have hδd : ∀ i : Fin 3,δ≤d i := by
    intro i
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let r := 1/2-δ/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hr' : r<1/2 := by dsimp [r]; linarith
  obtain ⟨X,hX,hXp,hXe⟩ := exists_periodic_position_box (chamberCorner s) hr hr'
  have hsF := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hcorner := (isMinimizerAt_chamber_vertex_order hV hE hm hμ ha hsgc hs).1
  rw [chamberVertex_bottom] at hcorner
  refine ⟨X,hX,hXp,?_⟩
  intro x hx
  let a := quotientMap x
  let y := shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s
  have hyq : quotientMap y=quotientMap x := by
    change quotientMap (shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s)=a
    rw [quotientMap_add,quotientMap_shortestLift,sub_add_cancel]
  have hyb : ∀ i : Fin 3,|y i-chamberCorner s i| ≤ r := by
    intro i
    have hclosed : quotientMap (chamberFoldLift s a)∈closure (openRepresentative E) :=
      (chamberFoldLift_mem_iff (reflection_invariant_closure hsF) s a).mpr (frontier_subset_closure hx)
    have hgi := hgap i (chamberFoldLift s a) (chamberFoldLift_mem s a) hclosed
    rw [chamberFoldLift_apply] at hgi
    change |shortestLift (a-quotientMap (chamberCorner s)) i+chamberCorner s i-chamberCorner s i| ≤ r
    simp only [add_sub_cancel_right]
    dsimp [r]
    linarith [hδd i]
  have hyS : quotientMap y∈frontier (openRepresentative E) := by rwa [hyq]
  have hyne : y≠chamberCorner s := by
    intro he
    rw [he,frontier,(isOpen_openRepresentative E).interior_eq] at hyS
    exact hyS.2 hcorner
  have hnxy : N x=N y := by
    rw [← periodic_representative hp x,← periodic_representative hp y,hyq]
  have hXxy : X x=X y := by
    rw [← periodic_representative hXp x,← periodic_representative hXp y,hyq]
  have hDxy : fderiv ℝ X x=fderiv ℝ X y := by
    rw [← periodic_representative (fderiv_periodic hXp) x,
      ← periodic_representative (fderiv_periodic hXp) y,hyq]
  have he := hXe y hyb
  constructor
  · rw [hDxy,he.fderiv_eq]
    exact ((hasFDerivAt_id y).sub_const (chamberCorner s)).fderiv
  · rw [hnxy,hXxy,he.eq_of_nhds]
    exact isMinimizerAt_chamber_support_positive hV hE hm hμ hN hp ha hs hsg hyS
      (fun i => (hyb i).trans_lt hr') hyne

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_one_vertex_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ (c : Cover) (r : ℝ),0 < r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  obtain ⟨ν,H,M,hM,hpM,hν,haM,hb,hCMC,_,hj⟩ :=
    Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  have he : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → N x=M x := by
    intro x hx
    exact isMinimizerAt_normal_local_ae_eq hV hV hE hE hm hm isOpen_univ (Filter.EventuallyEq.rfl)
      hμ hν hN hM hp hpM ha haM x ⟨hx,mem_univ _⟩
  have hsgM : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<M x i := by
    intro x i hx
    rw [← he x hx.1]
    exact hsg x i hx
  obtain ⟨X,hX,hpX,hXb⟩ := isMinimizerAt_one_vertex_position hV hE hm hν hM hpM haM hs hsgM hv
  have hνU := hν.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hνU
  exact isMinimizerAt_positive_position_spherical hV hE hm hc hν hM hpM haM hb hCMC hj hX hpX
    (hbd.mono fun z hz => (hXb z.1 hz).1) (hbd.mono fun z hz => (hXb z.1 hz).2)

theorem isMinimizerAt_one_vertex_standard_ball_oai {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    V≤4*Real.pi/81 ∧ CongruentAE E (canonicalBall V) := by
  obtain ⟨c,r,hr,hr',hbd⟩ := isMinimizerAt_one_vertex_spherical
    ⟨hV.1,by linarith [hV.2]⟩ hE hm hc hμ hN hp ha hs hsg hv
  exact isMinimizerAt_spherical_standard_ball hV hE hm hr hr' hbd

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball_oai := @OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball_oai
