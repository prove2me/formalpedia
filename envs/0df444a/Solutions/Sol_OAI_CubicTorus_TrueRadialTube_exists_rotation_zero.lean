-- Prove2me | solution 1 for OAI.CubicTorus.TrueRadialTube.exists_rotation_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:56:26.350915+00:00
-- url     : https://prove2.me/submissions/805c2261-9e15-42d1-a978-31827c41ea1b

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_full_jacobi_system
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_H1_jacobi_unique_continuation
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_rotation_jacobi_from_germs

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
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

end CubicTorus

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_UnitAngle
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

lemma unitAngle_norm (t : ℝ) : ‖unitAngle t‖=1 := by simp [unitAngle,Complex.norm_exp]

lemma unitAngle_periodic : Function.Periodic unitAngle 1 := by
  intro x
  change Complex.exp ((2*Real.pi*(x+1) : ℝ)*Complex.I)=_
  rw [show ((2*Real.pi*(x+1) : ℝ) : ℂ)*Complex.I=
    ((2*Real.pi*x : ℝ) : ℂ)*Complex.I+2*(Real.pi : ℂ)*Complex.I by push_cast; ring]
  exact Complex.exp_periodic _

lemma unitAngle_deriv (t : ℝ) :
    HasDerivAt unitAngle (((2*Real.pi : ℝ)*Complex.I)*unitAngle t) t := by
  have hd := ((((hasDerivAt_id t).const_mul (2*Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp [unitAngle,id_eq,mul_comm]

lemma unitAngle_continuous : Continuous unitAngle :=
  continuous_iff_continuousAt.mpr fun t => (unitAngle_deriv t).continuousAt

end CubicTorus

end
end

section

noncomputable section
open Set Complex
open scoped Topology Real
namespace CubicTorus

lemma complexSquareGauge_pos {z : ℂ} (hz : z≠0) : 0 < complexSquareGauge z := by
  by_contra hh
  have hl : max |z.re| |z.im|≤0 := le_of_not_gt hh
  have h1 : z.re=0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hl) (abs_nonneg _))
  have h2 : z.im=0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hl) (abs_nonneg _))
  exact hz (Complex.ext h1 h2)

lemma unitAngle_ne_zero (t : ℝ) : unitAngle t≠0 := by
  intro hz
  have hh := unitAngle_norm t
  simp [hz] at hh

lemma complexSquareGauge_continuous : Continuous complexSquareGauge :=
  Complex.continuous_re.abs.max Complex.continuous_im.abs

lemma complexSquareGauge_smul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    complexSquareGauge (r • z)=r*complexSquareGauge z := by
  simp only [complexSquareGauge,Complex.smul_re,Complex.smul_im,smul_eq_mul,abs_mul,abs_of_nonneg hr]
  exact (mul_max_of_nonneg _ _ hr).symm

end CubicTorus

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

theorem exists_periodic_smooth_separator {A B : Set Torus} (hA : IsCompact A)
    (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧
      (∀ x,φ x∈Icc 0 1) ∧
      (∀ x,quotientMap x∈A → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      (∀ x,quotientMap x∈B → ∀ᶠ y in 𝓝 x,φ y=0) := by
  classical
  have hcut (a : A) := exists_periodic_local_cutoff a.1 hB.isOpen_compl
    (show a.1∈Bᶜ from fun hb ↦ Set.disjoint_left.mp hAB a.2 hb)
  choose φ hφ hp hb hW0 hzero using hcut
  choose W hW hWa hone using hW0
  obtain ⟨s,hs⟩ := hA.elim_finite_subcover W hW (fun a ha ↦ mem_iUnion.mpr ⟨⟨a,ha⟩,hWa ⟨a,ha⟩⟩)
  let ψ : Cover → ℝ := fun x ↦ 1-∏ a∈s,(1-φ a x)
  refine ⟨ψ,contDiff_const.sub (contDiff_prod (fun a _ ↦ contDiff_const.sub (hφ a))),?_,?_,?_,?_⟩
  · intro m x
    simp only [ψ,hp]
  · intro x
    have hn : 0≤∏ a∈s,(1-φ a x) := Finset.prod_nonneg fun a _ ↦ sub_nonneg.mpr (hb a x).2
    have hu : (∏ a∈s,(1-φ a x))≤1 := Finset.prod_le_one (fun a _ ↦ sub_nonneg.mpr (hb a x).2)
      (fun a _ ↦ by linarith [(hb a x).1])
    exact ⟨by dsimp [ψ]; linarith,by dsimp [ψ]; linarith⟩
  · intro x hx
    obtain ⟨a,has,hxa⟩ := mem_iUnion₂.mp (hs hx)
    filter_upwards [hone a x hxa] with y hy
    dsimp [ψ]
    rw [Finset.prod_eq_zero has (by rw [hy,sub_self]),sub_zero]
  · intro x hx
    have hn : ∀ᶠ y in 𝓝 x,∀ a∈s,φ a y=0 := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro a ha
      exact hzero a x (by simpa using hx)
    filter_upwards [hn] with y hy
    dsimp [ψ]
    have he : (∏ a∈s,(1-φ a y))=1 := Finset.prod_eq_one (fun a ha ↦ by rw [hy a ha,sub_zero])
    rw [he,sub_self]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
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

lemma surfaceJacobiB_symm (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q u v=surfaceJacobiB μ q v u := by
  have he : ⟪surfaceMultiplier μ q u.1,v.1⟫=⟪surfaceMultiplier μ q v.1,u.1⟫ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv
    change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hu
    change (q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hv
    change ⟪(q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,v.1 z⟫ =
      ⟪(q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,u.1 z⟫
    rw [hu,hv]
    simp only [smul_eq_mul,Pi.mul_apply,RCLike.inner_apply,RCLike.conj_to_real]
    ring
  unfold surfaceJacobiB
  rw [he,real_inner_comm u.2 v.2]

lemma surfaceJacobiB_add_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u+v) w=surfaceJacobiB μ q u w+surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_add,Prod.snd_add,map_add,inner_add_left]
  ring

lemma surfaceJacobiB_smul_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (c : ℝ) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (c • u) v=c*surfaceJacobiB μ q u v := by
  change ⟪c • u.2,v.2⟫-⟪surfaceMultiplier μ q (c • u.1),v.1⟫ =
    c*(⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫)
  simp only [map_smul,real_inner_smul_left]
  ring

theorem surfaceJacobi_zero_polarizes (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (S : Submodule ℝ (SurfaceJet μ))
    (hs : ∀ u∈S,0 ≤ surfaceJacobiB μ q u u)
    {u : SurfaceJet μ} (hu : u∈S) (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈S) : surfaceJacobiB μ q u v=0 := by
  have hquad (t : ℝ) : 0≤2*t*surfaceJacobiB μ q u v+t^2*surfaceJacobiB μ q v v := by
    have h := hs (u+t • v) (S.add_mem hu (S.smul_mem t hv))
    rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
      surfaceJacobiB_symm μ q u (u+t • v),surfaceJacobiB_add_left,
      surfaceJacobiB_smul_left,surfaceJacobiB_symm μ q v (u+t • v),
      surfaceJacobiB_add_left,surfaceJacobiB_smul_left,hz,
      surfaceJacobiB_symm μ q v u] at h
    nlinarith only [h]
  by_contra h
  let a := surfaceJacobiB μ q u v
  let b := surfaceJacobiB μ q v v
  have hb : 0≤b := hs v hv
  have hd : 0<b+1 := by linarith
  have hh := hquad (-a/(b+1))
  change 0≤2*(-a/(b+1))*a+(-a/(b+1))^2*b at hh
  have hh' := mul_nonneg hh (sq_nonneg (b+1))
  have he : (2*(-a/(b+1))*a+(-a/(b+1))^2*b)*(b+1)^2= -a^2*(b+2) := by
    field_simp [hd.ne']
    ring
  rw [he] at hh'
  have ha : 0<a^2 := sq_pos_of_ne_zero h
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceMean μ (surfaceSmoothJet μ f)=(∫ z,f.val z.1 ∂(μ : Measure NormalBundle)) := by
  change ⟪(ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue smoothScalarOne),
    (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f)⟫=_
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change f.val z.1 * (starRingEnd ℝ) 1=f.val z.1
  simp

lemma surfaceMean_one (μ : FiniteMeasure NormalBundle) :
    surfaceMean μ (surfaceOne μ)=(μ : Measure NormalBundle).real univ := by
  rw [surfaceOne,surfaceMean_of_smooth]
  simp [smoothScalarOne,integral_const,smul_eq_mul]

lemma surfaceOne_mem (μ : FiniteMeasure NormalBundle) : surfaceOne μ∈surfaceH1 μ :=
  subset_closure (LinearMap.mem_range_self _ smoothScalarOne)

lemma surfaceMean_center (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0) (u : SurfaceJet μ) :
    surfaceMean μ (surfaceCenter μ u)=0 := by
  simp only [surfaceCenter,map_sub,map_smul,smul_eq_mul,surfaceMean_one]
  field_simp [hm]
  ring

lemma surfaceCenter_mem (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) : surfaceCenter μ u∈surfaceH1 μ :=
  (surfaceH1 μ).sub_mem hu ((surfaceH1 μ).smul_mem _ (surfaceOne_mem μ))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_zero_mode_constant (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) :
    ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=
      (surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ)*surfaceMean μ v := by
  intro v hv
  have hpoly : ∀ w∈surfaceH1ZeroMean μ,0 ≤ surfaceJacobiB μ q w w := by
    intro w hw
    exact hs w hw.1 hw.2
  have hu' : u∈surfaceH1ZeroMean μ := ⟨hu,hmean⟩
  have hw' : surfaceCenter μ v∈surfaceH1ZeroMean μ :=
    ⟨surfaceCenter_mem μ hv,surfaceMean_center μ hm v⟩
  have hp := surfaceJacobi_zero_polarizes μ q (surfaceH1ZeroMean μ) hpoly hu' hz hw'
  have he : v=surfaceCenter μ v+(surfaceMean μ v/(μ : Measure NormalBundle).real univ) • surfaceOne μ := by
    simp [surfaceCenter]
  rw [surfaceJacobiB_symm μ q u v,he,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q (surfaceCenter μ v) u,hp,
    surfaceJacobiB_symm μ q (surfaceOne μ) u,zero_add]
  rw [map_add,map_smul,surfaceMean_center μ hm,surfaceMean_one]
  simp only [zero_add,smul_eq_mul]
  field_simp [hm]

theorem surfaceH1_zero_mode_homogeneous (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈surfaceH1 μ) (hvmean : surfaceMean μ v≠0)
    (huv : surfaceJacobiB μ q u v=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  have hc := surfaceH1_zero_mode_constant μ hm q hs hu hmean hz
  have hh := hc v hv
  rw [huv] at hh
  have hz' : surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ=0 :=
    (mul_eq_zero.mp hh.symm).resolve_right hvmean
  intro w hw
  rw [hc w hw,hz',zero_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_positive_patch_test {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Torus} (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty) :
    ∃ f : smoothPeriodicScalars,0 < surfaceMean μ (surfaceSmoothJet μ f) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0 := by
  obtain ⟨a,haU,hab⟩ := ha
  obtain ⟨φ,hφ,hp,hb,⟨W,hW,haW,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hU haU
  let f : smoothPeriodicScalars := ⟨φ,hφ,hp⟩
  refine ⟨f,?_,hzero⟩
  rw [surfaceMean_of_smooth]
  change 0<(∫ z,φ z.1 ∂(μ : Measure NormalBundle))
  by_contra! h
  have hz : (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg fun z ↦ (hb z.1).1)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ (hb z.1).1)
    (integrable_normal_base hφ.continuous μ)).mp hz
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous (continuous_const (y := (0 : ℝ))) hp
    (fun _ _ ↦ rfl) hae (representative a) (by simpa only [quotientMap_representative] using hab)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haW)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

lemma surfaceJacobiB_unused_patch (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (f : smoothPeriodicScalars)
    (hf : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=0 := by
  have hfv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hfg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hqu := Lp.coeFn_lpSMul (r := 2) q u.1
  have hgrad : ⟪u.2,(surfaceSmoothJet μ f).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfg] with z hz hgz
    by_cases hx : normalProjection z∈U
    · rw [(hz hx).2,inner_zero_left]
      rfl
    · change ((surfaceSmoothJet μ f).2) z=_ at hgz
      rw [hgz]
      have he : f.val=ᶠ[𝓝 (z.1 : Cover)]fun _ ↦ (0 : ℝ) := hf z.1 hx
      have hd := he.fderiv_eq (𝕜 := ℝ)
      have hg : gradient f.val z.1=0 := by simp [gradient,hd]
      change ⟪u.2 z,gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
      rw [hg]
      simp
  have hval : ⟪surfaceMultiplier μ q u.1,(surfaceSmoothJet μ f).1⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfv,hqu] with z hz hvz hqz
    change (surfaceMultiplier μ q u.1) z=_ at hqz
    by_cases hx : normalProjection z∈U
    · rw [hqz]
      simp [(hz hx).1]
    · change ((surfaceSmoothJet μ f).1) z=f.val z.1 at hvz
      rw [hvz,(hf z.1 hx).self_of_nhds,inner_zero_right]
      rfl
  simp only [surfaceJacobiB,hgrad,hval,sub_self]

theorem isMinimizerAt_H1_unused_patch_homogeneous {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) {U : Set Torus}
    (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty)
    (hzero : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  obtain ⟨f,hf,hfg⟩ := isMinimizerAt_positive_patch_test hV hE hmin hμ hU ha
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  exact surfaceH1_zero_mode_homogeneous μ hm q hs hu hmean hz
    (subset_closure (LinearMap.mem_range_self _ f)) hf.ne'
    (surfaceJacobiB_unused_patch μ q hzero f hfg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_gradient_mul {f g : Cover → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Cover) :
    gradient (f*g) x=g x • gradient f x+f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    inner_gradient_left,inner_gradient_left]
  rw [fderiv_mul (hf x) (hg x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma smoothScalarGradient_mul (f g : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarMul f g) z=
      g.val z.1 • smoothScalarGradient f z+f.val z.1 • smoothScalarGradient g z := by
  change gradient (f.val*g.val) z.1-⟪(z.2 : Cover),gradient (f.val*g.val) z.1⟫ • (z.2 : Cover)=_
  rw [cover_gradient_mul (f.property.1.differentiable (by simp)) (g.property.1.differentiable (by simp)),
    inner_add_right,real_inner_smul_right,real_inner_smul_right,add_smul]
  change _=g.val z.1 • (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))+
    f.val z.1 • (gradient g.val z.1-⟪(z.2 : Cover),gradient g.val z.1⟫ • (z.2 : Cover))
  simp only [smul_sub,smul_smul]
  abel

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponentScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (x : Cover) :
    (normalComponentScalar N hN hp i).val x=N x i := by
  simp only [normalComponentScalar,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
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

lemma smoothTransition_deriv_zero_neg {t : ℝ} (ht : t<0) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [he.deriv_eq]
  simp

lemma smoothTransition_deriv_zero_gt {t : ℝ} (ht : 1<t) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [he.deriv_eq]
  simp

lemma positiveTruncCoeff_zero {t : ℝ} (ht : t≤0) : positiveTruncCoeff t=0 := by
  rcases ht.eq_or_lt with rfl|ht
  · simp [positiveTruncCoeff]
  · simp [positiveTruncCoeff,Real.smoothTransition.zero_of_nonpos ht.le,smoothTransition_deriv_zero_neg ht]

lemma positiveTruncCoeff_one {t : ℝ} (ht : 1<t) : positiveTruncCoeff t=1 := by
  simp [positiveTruncCoeff,Real.smoothTransition.one_of_one_le ht.le,smoothTransition_deriv_zero_gt ht]

lemma positiveTruncCoeff_bounded : ∃ K : ℝ,0≤K ∧ ∀ t,‖positiveTruncCoeff t‖≤K := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).continuous_deriv (by simp)
  have hc : Continuous positiveTruncCoeff := Real.smoothTransition.continuous.add (continuous_id.mul hd)
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max (max M 1) 0,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t∈Icc (-1:ℝ) 2
  · exact (hM t ht).trans ((le_max_left M 1).trans (le_max_left _ _))
  · rcases lt_or_gt_of_ne (show t≠(-1:ℝ) by intro he; subst t; exact ht (by norm_num)) with hlt|hgt
    · rw [positiveTruncCoeff_zero (by linarith),norm_zero]
      exact le_max_right _ _
    · have htwo : 2<t := lt_of_not_ge (fun h ↦ ht ⟨hgt.le,h⟩)
      rw [positiveTruncCoeff_one (by linarith),norm_one]
      exact (le_max_right M 1).trans (le_max_left _ _)

lemma positiveTrunc_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (positiveTrunc n) (positiveTruncCoeff (((n:ℝ)+1)*t)) t := by
  have hS := (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).differentiable (by simp)
  have h := (hasDerivAt_id t).mul ((hS _).hasDerivAt.comp t ((hasDerivAt_id t).const_mul ((n:ℝ)+1)))
  have he : 1*(Real.smoothTransition ∘ fun y : ℝ ↦ ((n:ℝ)+1)*id y) t+
      id t*(deriv Real.smoothTransition (((n:ℝ)+1)*id t)*(((n:ℝ)+1)*1))=
      positiveTruncCoeff (((n:ℝ)+1)*t) := by
    dsimp [positiveTruncCoeff]
    ring
  rw [he] at h
  exact h

lemma positiveTrunc_bound (n : ℕ) (t : ℝ) : ‖positiveTrunc n t‖≤‖t‖ := by
  rw [positiveTrunc,norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_bounded_convergence {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → NormalBundle → F)
    (g : NormalBundle → F) (hf : ∀ n,MemLp (f n) 2 (μ : Measure NormalBundle))
    (hg : MemLp g 2 (μ : Measure NormalBundle)) {M : ℝ} (hM : 0≤M)
    (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=
      ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp,hg.coeFn_toLp] with z hsub hfz hgz
    rw [hsub,Pi.sub_apply,hfz,hgz,real_inner_self_eq_norm_sq]
  have hi : Tendsto (fun n ↦ ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : NormalBundle ↦ (0:ℝ)) (fun _ : NormalBundle ↦ (2*M)^2)
      (fun n ↦ (((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2))
      (integrable_const _) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hfb n,hgb] with z hfz hgz
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : ‖f n z-g z‖≤2*M := (norm_sub_le _ _).trans (by linarith)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hM)).2 hb
    · filter_upwards [ht] with z hz
      simpa using (((hz.sub (tendsto_const_nhds (x := g z))).norm).pow 2)
  have hn : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
      simpa only [he] using hi
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma nodalEpsilon_pos (n : ℕ) : 0<nodalEpsilon n := by unfold nodalEpsilon; positivity

lemma separatedPositiveTrunc_zero (n : ℕ) {t : ℝ} (ht : t≤nodalEpsilon n) :
    separatedPositiveTrunc n t=0 ∧ positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=0 := by
  have hh : ((n:ℝ)+1)*(t-nodalEpsilon n)≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht)
  exact ⟨by simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.zero_of_nonpos hh],
    positiveTruncCoeff_zero hh⟩

lemma separatedPositiveTrunc_bound (n : ℕ) (t : ℝ) : ‖separatedPositiveTrunc n t‖≤‖t‖ := by
  by_cases ht : t≤nodalEpsilon n
  · rw [(separatedPositiveTrunc_zero n ht).1,norm_zero]
    exact norm_nonneg _
  · have he := nodalEpsilon_pos n
    exact (positiveTrunc_bound n (t-nodalEpsilon n)).trans (by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by linarith : 0<t-nodalEpsilon n),
        abs_of_pos (by linarith : 0<t)]
      linarith)

lemma separatedPositiveTrunc_tendsto (t : ℝ) :
    Tendsto (fun n ↦ separatedPositiveTrunc n t) atTop (𝓝 (max t 0)) ∧
    ∀ᶠ n : ℕ in atTop,positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=(if 0<t then 1 else 0) := by
  by_cases ht : 0<t
  · have hn : Tendsto (fun n : ℕ ↦ ((n:ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
    have he (n : ℕ) : ((n:ℝ)+1)*(t-nodalEpsilon n)=((n:ℝ)+1)*t-1 := by
      rw [nodalEpsilon,mul_sub,mul_inv_cancel₀ (by positivity : (n:ℝ)+1≠0)]
    have hc : ∀ᶠ n : ℕ in atTop,1<((n:ℝ)+1)*(t-nodalEpsilon n) := by
      filter_upwards [hn.eventually (eventually_gt_atTop 2)] with n hn
      rw [he]
      linarith
    refine ⟨?_,?_⟩
    · have hε : Tendsto nodalEpsilon atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      have hl : Tendsto (fun n ↦ t-nodalEpsilon n) atTop (𝓝 (max t 0)) := by
        simpa [max_eq_left ht.le] using tendsto_const_nhds.sub hε
      apply hl.congr'
      filter_upwards [hc] with n hn
      simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.one_of_one_le hn.le]
    · filter_upwards [hc] with n hn
      simp [positiveTruncCoeff_one hn,ht]
  · have hz (n : ℕ) := separatedPositiveTrunc_zero n (le_trans (not_lt.mp ht) (nodalEpsilon_pos n).le)
    refine ⟨?_,?_⟩
    · simpa only [(hz _).1,max_eq_right (not_lt.mp ht)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
    · filter_upwards [] with n
      simp only [(hz n).2,ite_eq_right ht]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SmoothScalarSeparatedTrunc
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

lemma gradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (x : Cover) :
    gradient (smoothScalarSeparatedTrunc f n).val x=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val x-nodalEpsilon n)) • gradient f.val x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  have h := (positiveTrunc_hasDerivAt n (f.val x-nodalEpsilon n)).hasFDerivAt.comp x
    ((f.property.1.differentiable (by simp) x).hasFDerivAt.sub_const (nodalEpsilon n))
  change (fderiv ℝ (positiveTrunc n ∘ fun y ↦ f.val y-nodalEpsilon n) x) v=_
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma smoothScalarGradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarSeparatedTrunc f n) z=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z := by
  change gradient (smoothScalarSeparatedTrunc f n).val z.1-
    ⟪(z.2 : Cover),gradient (smoothScalarSeparatedTrunc f n).val z.1⟫ • (z.2 : Cover)=_
  rw [gradient_separatedPositiveTrunc,real_inner_smul_right]
  change _=positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) •
    (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub,smul_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarGradient_of_constant_germ (f : smoothPeriodicScalars) {x : Cover} {c : ℝ}
    (hf : ∀ᶠ y in 𝓝 x,f.val y=c) (ν : NormalSphere) :
    gradient f.val x-⟪(ν : Cover),gradient f.val x⟫ • (ν : Cover)=0 := by
  have he : f.val=ᶠ[𝓝 x] fun _ ↦ c := hf
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hg : gradient f.val x=0 := by simp [gradient,hd]
  simp [hg]

theorem nodal_restriction_smooth_approximants (f : smoothPeriodicScalars)
    (S D : Set Torus)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    ∃ g : ℕ → smoothPeriodicScalars,∀ n (z : NormalBundle),normalProjection z∈S →
      (smoothScalarValue (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z) ∧
      (smoothScalarGradient (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦
          positiveTruncCoeff (((n:ℝ)+1)*(f.val w.1-nodalEpsilon n)) • smoothScalarGradient f w) z) := by
  classical
  have hsep (n : ℕ) := exists_periodic_smooth_separator (hA n) (hB n)
    (show Disjoint {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}
      {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)} from
        Set.disjoint_left.mpr (fun a ha hb ↦ hb.2.1 ha.2.1))
  choose φ hφ hp hb hone hzero using hsep
  let φs (n : ℕ) : smoothPeriodicScalars := ⟨φ n,hφ n,hp n⟩
  let g (n : ℕ) := smoothScalarMul (φs n) (smoothScalarSeparatedTrunc f n)
  refine ⟨g,?_⟩
  intro n z hz
  have hv : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hgrad : smoothScalarGradient (g n) z=
      separatedPositiveTrunc n (f.val z.1) • smoothScalarGradient (φs n) z+
      φ n z.1 • (positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z) := by
    rw [smoothScalarGradient_mul,smoothScalarGradient_separatedPositiveTrunc]
    rfl
  have hval : smoothScalarValue (g n) z=φ n z.1*separatedPositiveTrunc n (f.val z.1) := rfl
  by_cases hl : f.val z.1≤nodalEpsilon n
  · obtain ⟨ht,hc⟩ := separatedPositiveTrunc_zero n hl
    rw [hval,hgrad,ht,hc]
    constructor <;> by_cases hd : normalProjection z∈D <;> simp [hd,ht,hc]
  · have ha : nodalEpsilon n≤f.val (representative (normalProjection z)) := by rw [hv]; exact (not_le.mp hl).le
    by_cases hd : normalProjection z∈D
    · have hh := hone n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=1 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]
    · have hh := hzero n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=0 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_continuous_bounded_convergence_ae {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → C(NormalBundle,F))
    (g : NormalBundle → F) (hg : MemLp g 2 (μ : Measure NormalBundle))
    {M : ℝ} (hM : 0≤M) (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n))
      atTop (𝓝 (hg.toLp g)) := by
  have hf (n : ℕ) : MemLp (f n) 2 (μ : Measure NormalBundle) :=
    (f n).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (n : ℕ) : ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n)=
      (hf n).toLp (f n) := by
    apply Lp.ext
    exact (f n).coeFn_toLp (μ : Measure NormalBundle) |>.trans (hf n).coeFn_toLp.symm
  simpa only [he] using surfaceL2_bounded_convergence μ (fun n ↦ f n) g hf hg hM hfb hgb ht

theorem nodalSurfaceJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (S D : Set Torus) (hD : MeasurableSet D)
    (hpos : ∀ a∈D,0<f.val (representative a))
    (hμ : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈S)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    nodalSurfaceJet μ f D hD∈surfaceH1 μ := by
  classical
  obtain ⟨g,hg⟩ := nodal_restriction_smooth_approximants f S D hA hB
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have htval : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).1) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).1) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarValue (g n))
      (nodalSurfaceValue f D) (nodalSurfaceValue_memLp μ f D hD)
      (norm_nonneg (smoothScalarValue f))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).1]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact (separatedPositiveTrunc_bound n (f.val z.1)).trans ((smoothScalarValue f).norm_coe_le_norm z)
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simpa only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false] using
          (smoothScalarValue f).norm_coe_le_norm z
      · simp only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · filter_upwards [hμ] with z hz
      have he : (fun n ↦ smoothScalarValue (g n) z)=
          fun n ↦ (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z :=
        funext (fun n ↦ (hg n z hz).1)
      rw [he]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,nodalSurfaceValue]
        change Tendsto (fun n ↦ separatedPositiveTrunc n (f.val z.1)) atTop (𝓝 (f.val z.1))
        simpa only [max_eq_left hp.le] using
          (separatedPositiveTrunc_tendsto (f.val z.1)).1
      · simpa only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false,nodalSurfaceValue] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  obtain ⟨K,hK,hKb⟩ := positiveTruncCoeff_bounded
  have htgrad : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).2) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).2) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarGradient (g n))
      (nodalSurfaceGradient f D) (nodalSurfaceGradient_memLp μ f D hD)
      (mul_nonneg (show 0≤K+1 by linarith) (norm_nonneg (smoothScalarGradient f)))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,norm_smul]
        exact (mul_le_mul (hKb _) ((smoothScalarGradient f).norm_coe_le_norm z)
          (norm_nonneg _) hK).trans (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact ((smoothScalarGradient f).norm_coe_le_norm z).trans
          (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · filter_upwards [hμ] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [(separatedPositiveTrunc_tendsto (f.val z.1)).2] with n hn
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,hn,ite_eq_left hp,one_smul,nodalSurfaceGradient]
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,nodalSurfaceGradient]
  apply (surfaceSmoothJet μ).range.isClosed_topologicalClosure.mem_of_tendsto
    (htval.prodMk_nhds htgrad)
  filter_upwards [] with n
  exact subset_closure ⟨g n,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_superlevels (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsClosed S) (hD : IsPositiveNodalPiece f S D) :
    MeasurableSet D ∧ (∀ a∈D,0<f.val (representative a)) ∧
    (∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}) ∧
    (∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  have hP : MeasurableSet {a : Torus | a∈S ∧ 0<f.val (representative a)} :=
    hS.measurableSet.inter (isOpen_lt continuous_const hf).measurableSet
  refine ⟨by rw [hDU]; exact hP.inter hU.measurableSet,?_,?_,?_⟩
  · intro a ha
    rw [hDU] at ha
    exact ha.1.2
  · intro n
    have he : {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩C∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        rw [hDC] at hd
        exact ⟨⟨ha,hd.2⟩,hv⟩
      · rintro ⟨⟨ha,hc⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        rw [hDC]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hc⟩
    rw [he]
    exact ((hS.inter hC).inter (isClosed_le continuous_const hf)).isCompact
  · intro n
    have he : {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩Uᶜ∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        refine ⟨⟨ha,?_⟩,hv⟩
        intro hu
        apply hd
        rw [hDU]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hu⟩
      · rintro ⟨⟨ha,hu⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        intro hd
        rw [hDU] at hd
        exact hu hd.2
    rw [he]
    exact (hS.inter hU.isClosed_compl).inter (isClosed_le continuous_const hf)

theorem isMinimizerAt_positive_nodal_piece_H1 {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) :
    ∃ hDm : MeasurableSet D,nodalSurfaceJet μ f D hDm∈surfaceH1 μ := by
  obtain ⟨hDm,hpos,hA,hB⟩ := positiveNodalPiece_superlevels f isClosed_frontier hD
  refine ⟨hDm,nodalSurfaceJet_mem_surfaceH1 μ f (frontier (openRepresentative E)) D hDm hpos ?_ hA hB⟩
  exact normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_nodal_restriction (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceJacobiB μ q (surfaceSmoothJet μ f) (nodalSurfaceJet μ f D hD)=
      surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD) := by
  classical
  have hv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hpv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hpg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  unfold surfaceJacobiB
  congr 1
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg,hpg] with z hgz hpgz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hgz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hpgz
    rw [hgz,hpgz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceGradient,hd]
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    have hmf := Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ f).1
    have hmp := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
    filter_upwards [hv,hpv,hmf,hmp] with z hvz hpvz hmfz hmpz
    change (surfaceSmoothJet μ f).1 z=f.val z.1 at hvz
    change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hpvz
    change (surfaceMultiplier μ q (surfaceSmoothJet μ f).1) z=_ at hmfz
    change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmpz
    rw [hmfz,hmpz]
    simp only [smul_eq_mul,Pi.mul_apply,hvz,hpvz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceValue,smoothScalarValue,hd]

lemma surfaceJacobiB_disjoint_nodal (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f g : smoothPeriodicScalars)
    (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) (hDA : Disjoint D A) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ g A hA)=0 := by
  classical
  have hdv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hdg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  have hav := (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp
  have hag := (nodalSurfaceGradient_memLp μ g A hA).coeFn_toLp
  unfold surfaceJacobiB
  have hx : ⟪(nodalSurfaceJet μ f D hD).2,(nodalSurfaceJet μ g A hA).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hdg,hag] with z hdz haz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hdz
    change (nodalSurfaceJet μ g A hA).2 z=nodalSurfaceGradient g A z at haz
    rw [hdz,haz]
    by_cases hd : normalProjection z∈D
    · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
      simp [nodalSurfaceGradient,ha]
    · simp [nodalSurfaceGradient,hd]
  rw [hx,zero_sub,neg_eq_zero]
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hm := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
  filter_upwards [hdv,hav,hm] with z hdz haz hmz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  change (nodalSurfaceJet μ g A hA).1 z=nodalSurfaceValue g A z at haz
  change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmz
  rw [hmz]
  simp only [smul_eq_mul,Pi.mul_apply,hdz,haz]
  by_cases hd : normalProjection z∈D
  · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
    simp [nodalSurfaceValue,ha]
  · simp [nodalSurfaceValue,hd]

lemma nodalSurfaceJet_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) (hm : nodalSurfaceJet μ f D hD∈surfaceH1 μ)
    (hj : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) w=0) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD)=0 := by
  rw [← surfaceJacobiB_nodal_restriction]
  exact hj _ hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_nodal (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceMean μ (nodalSurfaceJet μ f D hD)=∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle) := by
  change ⟪(surfaceOne μ).1,(nodalSurfaceJet μ f D hD).1⟫=_
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv := (smoothScalarValue smoothScalarOne).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hd := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  filter_upwards [hv,hd] with z hvz hdz
  change (surfaceOne μ).1 z=1 at hvz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  rw [hvz,hdz]
  simp

theorem isMinimizerAt_nodal_mean_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    0 < surfaceMean μ (nodalSurfaceJet μ f D hDm) := by
  classical
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hpos := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1
  have hp (z : NormalBundle) : 0≤nodalSurfaceValue f D z := by
    by_cases hd : normalProjection z∈D
    · have hh := hpos _ hd
      rw [hv z] at hh
      simpa [nodalSurfaceValue,hd,smoothScalarValue] using hh.le
    · simp [nodalSurfaceValue,hd]
  rw [surfaceMean_nodal]
  by_contra! h
  have hz : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg hp)
  have hae := (integral_eq_zero_iff_of_nonneg hp
    ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))).mp hz
  obtain ⟨U,hU,hDU⟩ := hD.1
  obtain ⟨a,ha⟩ := hDn
  have ha' := ha
  rw [hDU] at ha'
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  let W : Set Torus := U∩{a : Torus | 0<f.val (representative a)}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_const hf)
  have haW : a∈W := ⟨ha'.2,ha'.1.2⟩
  obtain ⟨φ,hφ,hper,hb,⟨T,hT,haT,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hW haW
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hφae : ∀ᵐ z ∂(μ : Measure NormalBundle),φ z.1=0 := by
    filter_upwards [hbd,hae] with z hzbd hz0
    by_cases hzW : normalProjection z∈W
    · have hzD : normalProjection z∈D := by
        rw [hDU]
        exact ⟨⟨hzbd,hzW.2⟩,hzW.1⟩
      have hfz : 0<f.val z.1 := by
        have hh : 0<f.val (representative (normalProjection z)) := hzW.2
        rw [hv z] at hh
        exact hh
      have hf0 : f.val z.1=0 := by simpa [nodalSurfaceValue,hzD,smoothScalarValue] using hz0
      exact False.elim (hfz.ne' hf0)
    · exact (hzero z.1 hzW).self_of_nhds
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous
    (continuous_const (y := (0 : ℝ))) hper (fun _ _ ↦ rfl) hφae (representative a)
    (by simpa only [quotientMap_representative] using ha'.1.1)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haT)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceNodalBalance_mean (μ : FiniteMeasure NormalBundle) (u v : SurfaceJet μ) :
    surfaceMean μ (surfaceNodalBalance μ u v)=0 := by
  simp only [surfaceNodalBalance,map_add,map_smul,smul_eq_mul]
  ring

lemma surfaceNodalBalance_mem (μ : FiniteMeasure NormalBundle) {u v : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hv : v∈surfaceH1 μ) : surfaceNodalBalance μ u v∈surfaceH1 μ :=
  (surfaceH1 μ).add_mem ((surfaceH1 μ).smul_mem _ hu) ((surfaceH1 μ).smul_mem _ hv)

lemma surfaceNodalBalance_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u v : SurfaceJet μ}
    (hu : surfaceJacobiB μ q u u=0) (hv : surfaceJacobiB μ q v v=0)
    (huv : surfaceJacobiB μ q u v=0) :
    surfaceJacobiB μ q (surfaceNodalBalance μ u v) (surfaceNodalBalance μ u v)=0 := by
  have hvu : surfaceJacobiB μ q v u=0 := by rw [surfaceJacobiB_symm]; exact huv
  unfold surfaceNodalBalance
  rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q u,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,hu,hvu,
    surfaceJacobiB_symm μ q v,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,huv,hv]
  ring

lemma nodalSurfaceJet_zero_outside (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (D U : Set Torus) (hD : MeasurableSet D) (hUD : Disjoint U D) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (nodalSurfaceJet μ f D hD).1 z=0 ∧ (nodalSurfaceJet μ f D hD).2 z=0 := by
  classical
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp] with z hvz hgz hz
  have hd : normalProjection z∉D := fun hd ↦ Set.disjoint_left.mp hUD hz hd
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hvz
  change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hgz
  rw [hvz,hgz]
  simp [nodalSurfaceValue,nodalSurfaceGradient,hd]

lemma surfaceNodalBalance_zero_patch (μ : FiniteMeasure NormalBundle)
    {u v : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (hv : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → v.1 z=0 ∧ v.2 z=0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (surfaceNodalBalance μ u v).1 z=0 ∧ (surfaceNodalBalance μ u v).2 z=0 := by
  have h1 := Lp.coeFn_add (surfaceMean μ v • u.1) ((-surfaceMean μ u) • v.1)
  have h2 := Lp.coeFn_add (surfaceMean μ v • u.2) ((-surfaceMean μ u) • v.2)
  filter_upwards [hu,hv,h1,h2,Lp.coeFn_smul (surfaceMean μ v) u.1,
    Lp.coeFn_smul (-surfaceMean μ u) v.1,Lp.coeFn_smul (surfaceMean μ v) u.2,
    Lp.coeFn_smul (-surfaceMean μ u) v.2] with z huz hvz h1z h2z h3z h4z h5z h6z hz
  obtain ⟨huv,hug⟩ := huz hz
  obtain ⟨hvv,hvg⟩ := hvz hz
  constructor
  · change (surfaceMean μ v • u.1+(-surfaceMean μ u) • v.1) z=0
    rw [h1z]
    simp only [Pi.add_apply,h3z,h4z,Pi.smul_apply,huv,hvv,smul_zero,add_zero]
  · change (surfaceMean μ v • u.2+(-surfaceMean μ u) • v.2) z=0
    rw [h2z]
    simp only [Pi.add_apply,h5z,h6z,Pi.smul_apply,hug,hvg,smul_zero,add_zero]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Tangency
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

lemma continuous_indicator_positive_piece {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {D U C : Set X}
    (hU : IsOpen U) (hC : IsClosed C)
    (hDU : D={x | 0<f x}∩U) (hDC : D={x | 0<f x}∩C) :
    Continuous (D.indicator f) := by
  have hDo : IsOpen D := by rw [hDU]; exact (isOpen_lt continuous_const hf).inter hU
  have hclosureC : closure D⊆C := closure_minimal (by rw [hDC]; exact inter_subset_right) hC
  have hclosure0 : closure D⊆{x | 0≤f x} := by
    apply closure_minimal
    · intro x hx
      rw [hDC] at hx
      exact (show 0 < f x from hx.1).le
    · exact isClosed_le continuous_const hf
  apply continuous_indicator _ hf.continuousOn
  intro x hx
  have hxc := hclosureC (frontier_subset_closure hx)
  have hx0 := hclosure0 (frontier_subset_closure hx)
  have hxD : x∉D := by
    rw [hDo.frontier_eq] at hx
    exact hx.2
  have hxnp : ¬0<f x := by
    intro hpos
    apply hxD
    rw [hDC]
    exact ⟨hpos,hxc⟩
  exact le_antisymm (le_of_not_gt hxnp) hx0

theorem IsPositiveNodalPiece.continuous_value (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    ContinuousOn (D.indicator (fun a => f.val (representative a))) S := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  let F : S → ℝ := fun a => f.val (representative a)
  let A : Set S := Subtype.val ⁻¹' D
  have hF : Continuous F :=
    (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val
  have hAU : A={a : S | 0<F a}∩(Subtype.val ⁻¹' U) := by
    ext a
    simp only [A,mem_preimage,hDU,mem_inter_iff,mem_ofPred_eq,F,a.property,true_and]
  have hAC : A={a : S | 0<F a}∩(Subtype.val ⁻¹' C) := by
    ext a
    simp only [A,mem_preimage,hDC,mem_inter_iff,mem_ofPred_eq,F,a.property,true_and]
  have hh := continuous_indicator_positive_piece hF
    (hU.preimage continuous_subtype_val) (hC.preimage continuous_subtype_val) hAU hAC
  rw [continuousOn_iff_continuous_domRestrict]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  by_cases ha : (a : Torus) ∈ D <;> simp [A, F, ha]

lemma nodalSurfaceValue_descent (f : smoothPeriodicScalars) (D : Set Torus) (z : NormalBundle) :
    nodalSurfaceValue f D z=
      D.indicator (fun a => f.val (representative a)) (normalProjection z) := by
  have hv : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 _
  by_cases hd : normalProjection z∈D
  · simp only [nodalSurfaceValue,indicator_of_mem (show z∈normalProjection ⁻¹' D from hd),
      indicator_of_mem hd,smoothScalarValue,ContinuousMap.coe_mk,hv]
  · simp [nodalSurfaceValue,hd]

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

lemma coordinateReflection_fixed_of_sine_zero (i : Fin 3) {a : Torus}
    (ha : coordinateSine i (representative a)=0) : coordinateReflection i a=a := by
  ext j
  by_cases hji : j=i
  · subst j
    simp only [coordinateReflection_apply,ite_true]
    change -a i=a i
    have hz : Real.sin (Real.pi*(2*representative a i))=0 := by
      simpa only [coordinateSine,mul_assoc,mul_left_comm,mul_comm] using ha
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz
    have he : (2 : ℝ)*representative a i=(k : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      exact hk.symm.trans (mul_comm _ _)
    have hh : ((2*representative a i : ℝ) : AddCircle (1 : ℝ))=0 := by
      rw [he]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k,by simp⟩
    have haa : a i+a i=0 := by
      rw [← quotientMap_representative a]
      change ((representative a i : ℝ) : AddCircle (1 : ℝ))+((representative a i : ℝ) : AddCircle (1 : ℝ))=0
      rw [← AddCircle.coe_add,← two_mul]
      exact hh
    exact (neg_eq_iff_add_eq_zero).mpr haa
  · simp [hji]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceNodalBalanceValue_measurable (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    Measurable (surfaceNodalBalanceValue μ f g D A hD hA) :=
  ((continuous_periodic_descent f.property.1.continuous f.property.2).measurable.indicator hD).const_mul _ |>.add
    (((continuous_periodic_descent g.property.1.continuous g.property.2).measurable.indicator hA).const_mul _)

lemma surfaceNodalBalanceValue_continuousOn (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) {S D A : Set Torus} (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hd : IsPositiveNodalPiece f S D) (ha : IsPositiveNodalPiece g S A) :
    ContinuousOn (surfaceNodalBalanceValue μ f g D A hD hA) S :=
  ((hd.continuous_value f).const_mul _).add ((ha.continuous_value g).const_mul _)

lemma surfaceNodalBalanceValue_ae (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    ((surfaceNodalBalance μ (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ g A hA)).1 :
      NormalBundle → ℝ) =ᵐ[(μ : Measure NormalBundle)] surfaceNodalBalanceValue μ f g D A hD hA ∘ normalProjection := by
  let d := nodalSurfaceJet μ f D hD
  let a := nodalSurfaceJet μ g A hA
  filter_upwards [Lp.coeFn_add (surfaceMean μ a • d.1) ((-surfaceMean μ d) • a.1),
    Lp.coeFn_smul (surfaceMean μ a) d.1,Lp.coeFn_smul (-surfaceMean μ d) a.1,
    (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp] with z h1 h2 h3 h4 h5
  change d.1 z=nodalSurfaceValue f D z at h4
  change a.1 z=nodalSurfaceValue g A z at h5
  change (surfaceMean μ a • d.1+(-surfaceMean μ d) • a.1) z=_
  rw [h1]
  simp only [Pi.add_apply,h2,h3,Pi.smul_apply,smul_eq_mul,h4,h5,nodalSurfaceValue_descent]
  rfl

lemma surfaceNodalBalanceValue_on_left (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hDA : Disjoint D A) {x : Torus} (hx : x∈D) :
    surfaceNodalBalanceValue μ f g D A hD hA x=
      surfaceMean μ (nodalSurfaceJet μ g A hA)*f.val (representative x) := by
  have hn : x∉A := fun ha => Set.disjoint_left.mp hDA hx ha
  simp [surfaceNodalBalanceValue,hx,hn]

lemma surfaceNodalBalanceValue_nonpos (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) {S D A : Set Torus} (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hd : IsPositiveNodalPiece f S D) (ha : IsPositiveNodalPiece f S A)
    {x : Torus} (hx : f.val (representative x)≤0) :
    surfaceNodalBalanceValue μ f f D A hD hA x=0 := by
  have hdx : x∉D := by
    intro h
    obtain ⟨U,_,he⟩ := hd.1
    rw [he] at h
    exact (not_lt_of_ge hx) h.1.2
  have hax : x∉A := by
    intro h
    obtain ⟨U,_,he⟩ := ha.1
    rw [he] at h
    exact (not_lt_of_ge hx) h.1.2
  simp [surfaceNodalBalanceValue,hdx,hax]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma IsPositiveNodalPiece.eq_inter_open (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    ∃ W : Set Torus,IsOpen W ∧ D=S∩W := by
  obtain ⟨U,hU,hDU⟩ := hD.1
  refine ⟨{a | 0<f.val (representative a)}∩U,
    (isOpen_lt continuous_const (continuous_periodic_descent f.property.1.continuous f.property.2)).inter hU,?_⟩
  rw [hDU]
  ext a
  simp only [mem_inter_iff,mem_ofPred_eq,and_assoc]

lemma IsPositiveNodalPiece.subset (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) : D⊆S := by
  obtain ⟨W,_,he⟩ := hD.eq_inter_open f
  rw [he]
  exact inter_subset_left

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma descent_coordinateSine_reflection (i : Fin 3) (a : Torus) :
    coordinateSine i (representative (coordinateReflection i a))= -coordinateSine i (representative a) := by
  rw [← quotientMap_representative a,← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [quotientMap_representative]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
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

lemma coordinateSectionPoint_continuous_pair (c : Cover) :
    Continuous (fun p : ℝ × ℂ => coordinateSectionPoint c p.1 p.2) := by
  unfold coordinateSectionPoint
  fun_prop

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_SurfaceJacobiLocalization
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

lemma complex_eq_norm_smul_unitAngle (z : ℂ) :
    z=‖z‖ • unitAngle (Complex.arg z/(2*Real.pi)) := by
  have he : 2*Real.pi*(Complex.arg z/(2*Real.pi))=Complex.arg z := by
    field_simp [Real.pi_ne_zero]
  simp only [unitAngle,he,Complex.real_smul]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

lemma quotientMap_transverse_square (c : Cover) (q : Torus) :
    ∃ (t : ℝ) (z : ℂ),complexSquareGauge z≤1/2 ∧
      quotientMap (coordinateSectionPoint c t z)=q := by
  obtain ⟨x,rfl⟩ := quotientMap_surjective q
  let m : Fin 3 → ℤ := fun i => ⌊x i-c i+1/2⌋
  let y := x-latticeVector m
  let z : ℂ := ⟨y 1-c 1,y 2-c 2⟩
  have hb (i : Fin 3) : |y i-c i|≤1/2 := by
    have hl := Int.floor_le (x i-c i+1/2)
    have hu := Int.lt_floor_add_one (x i-c i+1/2)
    change |x i-(⌊x i-c i+1/2⌋ : ℝ)-c i|≤1/2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have he : coordinateSectionPoint c (y 0) z=y := by
    ext i
    fin_cases i <;> simp [z]
  refine ⟨y 0,z,max_le (hb 1) (hb 2),?_⟩
  rw [he]
  change quotientMap (x-latticeVector m)=quotientMap x
  rw [quotientMap_sub,quotientMap_latticeVector,sub_zero]

lemma norm_le_unitSquareScale_of_gauge {z : ℂ} (hz : complexSquareGauge z≤1/2) :
    ‖z‖≤unitSquareScale (Complex.arg z/(2*Real.pi)) := by
  let a := Complex.arg z/(2*Real.pi)
  have he := complex_eq_norm_smul_unitAngle z
  have hg : complexSquareGauge z=‖z‖*complexSquareGauge (unitAngle a) := by
    conv_lhs => rw [he]
    exact complexSquareGauge_smul (norm_nonneg _) _
  rw [hg] at hz
  change ‖z‖≤1/(2*complexSquareGauge (unitAngle a))
  apply (le_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))).mpr
  nlinarith

theorem TrueRadialTube.boundary_range {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hr : TrueRadialTube E c r) :
    Set.range (fun p : ℝ × ℝ => quotientMap (coordinateSectionPoint c p.1
      (r p • unitAngle p.2)))=frontier (openRepresentative E) := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    exact hr.2.2.2.2.1 p
  · intro hq
    obtain ⟨t,z,hz,he⟩ := quotientMap_transverse_square c q
    let a := Complex.arg z/(2*Real.pi)
    have hpolar : z=‖z‖ • unitAngle a := complex_eq_norm_smul_unitAngle z
    have hbound : ‖z‖≤unitSquareScale a := norm_le_unitSquareScale_of_gauge hz
    have hb : quotientMap (coordinateSectionPoint c t (‖z‖ • unitAngle a))∈
        frontier (openRepresentative E) := by rwa [← hpolar,he]
    rw [(isOpen_openRepresentative E).frontier_eq] at hb
    have hle : ‖z‖ ≤ r (t,a) := (hr.2.2.2.2.2.2.1 (t,a) ‖z‖ (norm_nonneg _) hbound).mp hb.1
    have hge : r (t,a)≤‖z‖ := le_of_not_gt (fun hh =>
      hb.2 ((hr.2.2.2.2.2.1 (t,a) ‖z‖ (norm_nonneg _) hbound).mpr hh))
    have hn : r (t,a)=‖z‖ := le_antisymm hge hle
    exact ⟨(t,a),by simpa only [hn,← hpolar] using he⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma pair_periodic_descend {X : Type*} [TopologicalSpace X] {f : ℝ × ℝ → X}
    (hf : Continuous f) (hp1 : ∀ t a,f (t+1,a)=f (t,a))
    (hp2 : ∀ t a,f (t,a+1)=f (t,a)) :
    ∃ F : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → X,Continuous F ∧
      ∀ (t a : ℝ),F ((t : AddCircle (1 : ℝ)),(a : AddCircle (1 : ℝ)))=f (t,a) := by
  let g : ℝ → AddCircle (1 : ℝ) → X := fun t => (show Function.Periodic (fun a => f (t,a)) 1 from hp2 t).lift
  have hgp : Function.Periodic g 1 := by
    intro t
    funext a
    induction a using QuotientAddGroup.induction_on with | H a =>
      exact hp1 t a
  let F : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → X := fun p => hgp.lift p.1 p.2
  have he (t a : ℝ) : F ((t : AddCircle (1 : ℝ)),(a : AddCircle (1 : ℝ)))=f (t,a) := rfl
  refine ⟨F,?_,he⟩
  have hq : IsOpenQuotientMap (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
  exact hf

lemma radial_point_gauge_lt {r a : ℝ} (hr : 0 < r) (hrs : r<unitSquareScale a) :
    complexSquareGauge (r • unitAngle a)<1/2 := by
  rw [complexSquareGauge_smul hr.le]
  have hd : 0 < complexSquareGauge (unitAngle a) := complexSquareGauge_pos (unitAngle_ne_zero a)
  change r<1/(2*complexSquareGauge (unitAngle a)) at hrs
  have hh := (lt_div_iff₀ (mul_pos (by norm_num) hd)).mp hrs
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_periodic_local_identity {R : ℝ} (hR : 0≤R) (hR' : R<1/2) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      ∀ x,|x|≤R → g =ᶠ[𝓝 x] id := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨(R+1/2)/2,((R+1/2)/2+1/2)/2,by linarith,by linarith⟩
  let f : ℝ → ℝ := fun x => b x*x
  have hc : HasCompactSupport f := b.hasCompactSupport.mul_right
  have hs : tsupport f ⊆ Ioo ((0 : ℝ)-1/2) (0+1/2) := by
    intro x hx
    have hh : x∈tsupport (b : ℝ → ℝ) := tsupport_mul_subset_left hx
    rw [b.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    change |x|≤((R+1/2)/2+1/2)/2 at hh
    exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩
  refine ⟨circlePeriodize f,circlePeriodize_contDiff (b.contDiff.mul contDiff_id) hc,
    circlePeriodize_periodic f,?_⟩
  intro x hx
  have hb : (b : ℝ → ℝ) =ᶠ[𝓝 x] 1 := b.eventuallyEq_one_of_mem_ball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    change |x|<(R+1/2)/2
    linarith)
  have hp := circlePeriodize_eventuallyEq hc hs (x := x)
    (show x∈Icc ((0 : ℝ)-1/2) (0+1/2) from
      ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2]⟩)
  filter_upwards [hp,hb] with y hy hby
  simpa [f,hby] using hy

theorem TrueRadialTube.uniform_square_gap {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ R : ℝ,0≤R ∧ R<1/2 ∧
      ∀ p,complexSquareGauge (r p • unitAngle p.2)≤R := by
  let f : ℝ × ℝ → ℝ := fun p => complexSquareGauge (r p • unitAngle p.2)
  have hf : Continuous f := complexSquareGauge_continuous.comp
    (hr.1.continuous.smul (unitAngle_continuous.comp continuous_snd))
  obtain ⟨F,hF,he⟩ := pair_periodic_descend hf (by
    intro t a
    change complexSquareGauge (r (t+1,a) • unitAngle a)=_
    rw [hr.2.1]) (by
    intro t a
    change complexSquareGauge (r (t,a+1) • unitAngle (a+1))=_
    rw [hr.2.2.1,unitAngle_periodic])
  have hb (p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) : 0≤F p ∧ F p<1/2 := by
    rcases p with ⟨t,a⟩
    induction t using QuotientAddGroup.induction_on with | H t =>
      induction a using QuotientAddGroup.induction_on with | H a =>
        rw [he]
        refine ⟨(abs_nonneg _).trans (le_max_left _ _),?_⟩
        exact radial_point_gauge_lt (hr.2.2.2.1 (t,a)).1 (hr.2.2.2.1 (t,a)).2
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuousOn
  refine ⟨F p,(hb p).1,(hb p).2,?_⟩
  intro q
  change f (q.1,q.2)≤F p
  rw [← he q.1 q.2]
  exact hp (Set.mem_univ _)

lemma periodicCoordinate_germ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (j : Fin 3) (x : Cover) (m : ℤ)
    (he : g =ᶠ[𝓝 (x j-c j-m)] id) :
    (periodicCoordinate g hg hp c j).val =ᶠ[𝓝 x] (fun y => y j-c j-m) := by
  have ht : Continuous (fun y : Cover => y j-c j-(m : ℝ)) :=
    (EuclideanSpace.proj j).continuous.sub continuous_const |>.sub continuous_const
  have hh := he.comp_tendsto ht.continuousAt
  filter_upwards [hh] with y hy
  change g (y j-c j-m)=y j-c j-m at hy
  change g (y j-c j)=y j-c j-m
  have hp' := hp.sub_int_mul_eq (x := y j-c j) m
  simp only [mul_one] at hp'
  rw [hp'] at hy
  exact hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodicCoordinate_cross_derivative (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c x : Cover) {i j : Fin 3} (hij : i≠j) :
    fderiv ℝ (periodicCoordinate g hg hp c j).val x (EuclideanSpace.single i 1)=0 := by
  have hd := ((hg.differentiable (by simp) (x j-c j)).hasFDerivAt).comp x
    ((EuclideanSpace.proj j : Cover →L[ℝ] ℝ).hasFDerivAt.sub_const (c j))
  change HasFDerivAt (periodicCoordinate g hg hp c j).val
    ((fderiv ℝ g (x j-c j)).comp (EuclideanSpace.proj j)) x at hd
  rw [hd.fderiv]
  simp [Ne.symm hij]

lemma periodicRotation_divergence (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c x : Cover) :
    divergence (periodicRotation g hg hp c) x=0 := by
  have h₁ := (periodicCoordinate g hg hp c 1).property.1.differentiable (by simp) x
  have h₂ := (periodicCoordinate g hg hp c 2).property.1.differentiable (by simp) x
  unfold periodicRotation
  rw [divergence_sub_fields (h₁.smul_const _) (h₂.smul_const _),
    divergence_smul_const h₁,divergence_smul_const h₂,
    periodicCoordinate_cross_derivative g hg hp c x (by decide : (2 : Fin 3)≠1),
    periodicCoordinate_cross_derivative g hg hp c x (by decide : (1 : Fin 3)≠2),sub_self]

theorem periodicRotation_normal_flux_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1) (c : Cover) :
    (∫ z,⟪(z.2 : Cover),periodicRotation g hg hp c z.1⟫ ∂(μ : Measure NormalBundle))=0 := by
  have hF := periodicRotation_contDiff g hg hp c
  have hFp := periodicRotation_periodic g hg hp c
  obtain ⟨k,hk,hb⟩ := periodic_bounded hF.continuous hFp
  have hh := normalMeasure_flux hμ hF hFp (show 0<k+1 by linarith)
    (fun x => (hb x).trans (by linarith : k≤k+1))
  simpa only [normalTest,ContinuousMap.coe_mk,periodicRotation_divergence,integral_zero] using hh

theorem periodicRotationNormalScalar_mean_zero {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    surfaceMean μ (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp))=0 := by
  rw [surfaceMean_of_smooth,← periodicRotation_normal_flux_zero hμ g hg hp c]
  apply integral_congr_ae
  filter_upwards [ha] with z hz
  change ⟪N z.1,periodicRotation g hg hp c z.1⟫=⟪(z.2 : Cover),periodicRotation g hg hp c z.1⟫
  rw [hz]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalRotationWeak
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

lemma periodicRotationNormalScalar_eq (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x) :
    periodicRotationNormalScalar g hg hp c N hN hNp =
      smoothScalarMul (periodicCoordinate g hg hp c 1) (normalComponentScalar N hN hNp 2)-
        smoothScalarMul (periodicCoordinate g hg hp c 2) (normalComponentScalar N hN hNp 1) := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sub,Pi.sub_apply,smoothScalarMul,Pi.mul_apply,
    normalComponentScalar_apply,periodicRotationNormalScalar,periodicRotation]
  change ⟪N x, (periodicCoordinate g hg hp c 1).val x • EuclideanSpace.single 2 1-
    (periodicCoordinate g hg hp c 2).val x • EuclideanSpace.single 1 1⟫ =
    (periodicCoordinate g hg hp c 1).val x * (N x 2)-
    (periodicCoordinate g hg hp c 2).val x * (N x 1)
  simp only [inner_sub_right,real_inner_smul_right,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_MinimizerJacobiEquation
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

theorem isMinimizerAt_mean_zero_negative_point {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars)
    (hzero : surfaceMean μ (surfaceSmoothJet μ f)=0)
    {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    ∃ a∈frontier (openRepresentative E),f.val (representative a)<0 := by
  classical
  by_contra! hn
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hpos := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hDm hD hDn
  rw [surfaceMean_nodal] at hpos
  rw [surfaceMean_of_smooth] at hzero
  have hle : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle)) ≤
      ∫ z,f.val z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_mono_ae ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))
      ((smoothScalarValue f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [hbd] with z hz
    by_cases hd : normalProjection z∈D
    · simp only [nodalSurfaceValue,indicator_of_mem (show z∈normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,le_refl]
    · have hv : f.val (representative (normalProjection z))=f.val z.1 := periodic_representative f.property.2 _
      simpa only [nodalSurfaceValue,indicator_of_notMem (show z∉normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,hv] using hn (normalProjection z) hz
  linarith

theorem isMinimizerAt_general_positive_nodal_not_disjoint {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u)
    (f : smoothPeriodicScalars)
    (hfmean : surfaceMean μ (surfaceSmoothJet μ f)=0)
    (hj : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) z=0)
    {D A : Set Torus}
    (hD : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) D)
    (hA : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) A)
    (hDn : D.Nonempty) (hAn : A.Nonempty) : ¬Disjoint D A := by
  intro hDA
  obtain ⟨hDm,hdmem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hD
  obtain ⟨hAm,hamem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hA
  let d := nodalSurfaceJet μ f D hDm
  let a := nodalSurfaceJet μ f A hAm
  let u := surfaceNodalBalance μ d a
  have hdnull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f D hDm hdmem hj
  have hanull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f A hAm hamem hj
  have hnull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull (surfaceJacobiB_disjoint_nodal μ _ f f D A hDm hAm hDA)
  have humem : u∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hmean : surfaceMean μ u=0 := surfaceNodalBalance_mean μ d a
  have hapos : 0 < surfaceMean μ a := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hAm hA hAn
  obtain ⟨b,hbS,hbneg⟩ := isMinimizerAt_mean_zero_negative_point hV hE hmin hμ f hfmean hDm hD hDn
  let U : Set Torus := {b | f.val (representative b)<0}
  have hU : IsOpen U := isOpen_lt (continuous_periodic_descent f.property.1.continuous f.property.2) continuous_const
  have hbU : b∈U := hbneg
  have hUD : Disjoint U D := by
    rw [Set.disjoint_left]
    intro x hx hd
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hd
    exact (not_lt_of_ge hh.le) hx
  have hUA : Disjoint U A := by
    rw [Set.disjoint_left]
    intro x hx ha
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hA).2.1 x ha
    exact (not_lt_of_ge hh.le) hx
  have hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0 :=
    isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ _ hs humem hmean hnull
      hU ⟨b,hbU,hbS⟩ (surfaceNodalBalance_zero_patch μ
        (nodalSurfaceJet_zero_outside μ f D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ f A U hAm hUA))
  let F := surfaceNodalBalanceValue μ f f D A hDm hAm
  have hzU : U⊆relativeZeroNeighborhood (frontier (openRepresentative E)) F := by
    apply hU.subset_interior_iff.mpr
    intro x hx
    right
    exact surfaceNodalBalanceValue_nonpos μ f hDm hAm hD hA (le_of_lt hx)
  have hvan := isMinimizerAt_H1_jacobi_unique_continuation hV hE hmin hμ N hN hp hae hNu
    humem hhom (surfaceNodalBalanceValue_measurable μ f f D A hDm hAm)
    (surfaceNodalBalanceValue_continuousOn μ f f hDm hAm hD hA)
    (surfaceNodalBalanceValue_ae μ f f D A hDm hAm) hS ⟨b,hbS,hzU hbU⟩
  obtain ⟨x,hx⟩ := hDn
  have hz := hvan x (hD.subset f hx)
  rw [surfaceNodalBalanceValue_on_left μ f f D A hDm hAm hDA hx] at hz
  have hfp := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hx
  exact (mul_pos hapos hfp).ne' hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.frontier_preconnected {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    IsPreconnected (frontier (openRepresentative E)) := by
  rw [← hr.boundary_range]
  apply isPreconnected_range
  exact continuous_quotientMap.comp ((coordinateSectionPoint_continuous_pair c).comp
    (continuous_fst.prodMk (hr.1.continuous.smul (unitAngle_continuous.comp continuous_snd))))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FlatTranslation
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

lemma positiveNodalPiece_separator_positive (f : smoothPeriodicScalars)
    (S : Set Torus) (s : Torus → ℝ) (hs : Continuous s)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0) :
    IsPositiveNodalPiece f S {a | a ∈ S ∧ 0 < f.val (representative a) ∧ 0 < s a} := by
  constructor
  · refine ⟨{a | 0 < s a}, isOpen_lt continuous_const hs, ?_⟩
    ext a
    simp only [mem_ofPred_eq, mem_inter_iff]
    tauto
  · refine ⟨{a | 0 ≤ s a}, isClosed_le continuous_const hs, ?_⟩
    ext a
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨ha, hf, hsa⟩
      exact ⟨⟨ha, hf⟩, hsa.le⟩
    · rintro ⟨⟨ha, hf⟩, hsa⟩
      refine ⟨ha, hf, lt_of_le_of_ne hsa ?_⟩
      intro he
      exact (ne_of_gt hf) (hz a ha he.symm)

lemma positiveNodalPiece_separator_negative (f : smoothPeriodicScalars)
    (S : Set Torus) (s : Torus → ℝ) (hs : Continuous s)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0) :
    IsPositiveNodalPiece f S {a | a ∈ S ∧ 0 < f.val (representative a) ∧ s a < 0} := by
  simpa only [neg_pos] using positiveNodalPiece_separator_positive f S (fun a => -s a)
    hs.neg (fun a ha he => hz a ha (neg_eq_zero.mp he))

theorem double_reflection_nodal_vanish (f : smoothPeriodicScalars)
    (S : Set Torus) (r t : Torus → Torus) (s : Torus → ℝ)
    (hs : Continuous s)
    (hr : ∀ a ∈ S, r a ∈ S) (ht : ∀ a ∈ S, t a ∈ S)
    (hfr : ∀ a ∈ S, f.val (representative (r a)) = -f.val (representative a))
    (hft : ∀ a ∈ S, f.val (representative (t a)) = -f.val (representative a))
    (hsr : ∀ a, s (r a) = -s a) (hst : ∀ a, s (t a) = s a)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0)
    (hnodal : ∀ D A : Set Torus, IsPositiveNodalPiece f S D →
      IsPositiveNodalPiece f S A → D.Nonempty → A.Nonempty → ¬Disjoint D A) :
    ∀ a ∈ S, f.val (representative a) = 0 := by
  have hno : ¬ ∃ a ∈ S, 0 < f.val (representative a) := by
    rintro ⟨a, ha, hfa⟩
    let D : Set Torus := {a | a ∈ S ∧ 0 < f.val (representative a) ∧ 0 < s a}
    let A : Set Torus := {a | a ∈ S ∧ 0 < f.val (representative a) ∧ s a < 0}
    have hD := positiveNodalPiece_separator_positive f S s hs hz
    have hA := positiveNodalPiece_separator_negative f S s hs hz
    have hfb : 0 < f.val (representative (t (r a))) := by
      rw [hft (r a) (hr a ha), hfr a ha, neg_neg]
      exact hfa
    have hsb : s (t (r a)) = -s a := by rw [hst, hsr]
    have hsa : s a ≠ 0 := by
      intro he
      exact (ne_of_gt hfa) (hz a ha he)
    have hnon : D.Nonempty ∧ A.Nonempty := by
      rcases lt_or_gt_of_ne hsa with hneg | hpos
      · exact ⟨⟨t (r a), ht (r a) (hr a ha), hfb, by rw [hsb]; linarith⟩,
          ⟨a, ha, hfa, hneg⟩⟩
      · exact ⟨⟨a, ha, hfa, hpos⟩,
          ⟨t (r a), ht (r a) (hr a ha), hfb, by rw [hsb]; linarith⟩⟩
    apply hnodal D A hD hA hnon.1 hnon.2
    rw [Set.disjoint_left]
    intro b hb hc
    exact (not_lt_of_gt hb.2.2) hc.2.2
  intro a ha
  have hle : f.val (representative a) ≤ 0 := le_of_not_gt (fun h => hno ⟨a, ha, h⟩)
  have hge : 0 ≤ f.val (representative a) := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    apply hno
    refine ⟨r a, hr a ha, ?_⟩
    rw [hfr a ha]
    linarith
  exact le_antisymm hle hge

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_odd_periodic_local_identity {R : ℝ} (hR : 0 ≤ R) (hR' : R < 1/2) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      (∀ x, g (-x) = -g x) ∧ ∀ x, |x| ≤ R → g =ᶠ[𝓝 x] id := by
  obtain ⟨g, hg, hp, he⟩ := exists_periodic_local_identity hR hR'
  let f : ℝ → ℝ := fun x => (g x - g (-x))/2
  refine ⟨f, (hg.sub (hg.comp contDiff_id.neg)).div_const 2, ?_, ?_, ?_⟩
  · intro x
    change (g (x+1)-g (-(x+1)))/2=(g x-g (-x))/2
    rw [hp x]
    have h := hp.sub_eq (-x)
    convert congrArg (fun z : ℝ => (g x-z)/2) h using 1; congr 2; ring_nf
  · intro x
    dsimp [f]
    rw [neg_neg]
    ring
  · intro x hx
    have hneg := (he (-x) (by simpa only [abs_neg] using hx)).comp_tendsto
      (continuous_neg.continuousAt : Tendsto (fun y : ℝ => -y) (𝓝 x) (𝓝 (-x)))
    filter_upwards [he x hx, hneg] with y hy hny
    change (g y - g (-y))/2 = y
    change g y=y at hy
    change g (-y)= -y at hny
    rw [hy, hny]
    ring

theorem TrueRadialTube.odd_periodic_transverse_germs {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      (∀ x, g (-x) = -g x) ∧
      ∀ p, (g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id) := by
  obtain ⟨R, hR, hR', hb⟩ := hr.uniform_square_gap
  obtain ⟨g, hg, hp, ho, he⟩ := exists_odd_periodic_local_identity hR hR'
  exact ⟨g, hg, hp, ho, fun p =>
    ⟨he _ ((le_max_left _ _).trans (hb p)), he _ ((le_max_right _ _).trans (hb p))⟩⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem TrueRadialTube.exists_odd_rotation_nodal_restriction {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      (∀ x, g (-x) = -g x) ∧ IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      ∀ D A : Set Torus,
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,H,N,hN,hNp,hμ,ha,hu,hCMC,hs,hj⟩ := Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  obtain ⟨g,hg,hp,ho,he⟩ := hr.odd_periodic_transverse_germs
  have hzero := periodicRotationNormalScalar_mean_zero hμ g hg hp c N hN hNp ha
  have hrot : ∀ w ∈ surfaceH1 μ, surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp)) w = 0 := by
    rw [periodicRotationNormalScalar_eq]
    apply isMinimizerAt_rotation_jacobi_from_germs hV hE hm hμ hN hNp ha
      (fun x hx => (hu x hx).1) hCMC hj
    intro x hx
    rw [← hr.boundary_range] at hx
    obtain ⟨p,hpx⟩ := hx
    obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
    have h₁ : x 1-c 1-(m 1 : ℝ)=(r p • unitAngle p.2).re := by
      rw [hm]
      simp [latticeVector]
      ring
    have h₂ : x 2-c 2-(m 2 : ℝ)=(r p • unitAngle p.2).im := by
      rw [hm]
      simp [latticeVector]
      ring
    refine ⟨c 1+(m 1 : ℝ),c 2+(m 2 : ℝ),?_,?_⟩
    · simpa only [sub_add_eq_sub_sub] using
        periodicCoordinate_germ g hg hp c 1 x (m 1) (by rw [h₁]; exact (he p).1)
    · simpa only [sub_add_eq_sub_sub] using
        periodicCoordinate_germ g hg hp c 2 x (m 2) (by rw [h₂]; exact (he p).2)
  refine ⟨μ,N,hN,hNp,g,hg,hp,ho,hμ,ha,he,?_⟩
  intro D A hD hA hDn hAn
  exact isMinimizerAt_general_positive_nodal_not_disjoint hV hE hm hr.frontier_preconnected
    hμ N hN hNp ha (fun x hx => (hu x hx).1) hs
    (periodicRotationNormalScalar g hg hp c N hN hNp) hzero hrot hD hA hDn hAn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma odd_periodic_chamberCorner (g : ℝ → ℝ) (hp : Function.Periodic g 1)
    (ho : ∀ x, g (-x) = -g x) (b : Fin 3 → Bool) (i : Fin 3) (x : ℝ) :
    g (-x - chamberCorner b i) = -g (x - chamberCorner b i) := by
  cases hi : b i
  · simpa only [chamberCorner, hi, Bool.false_eq_true, ite_false, sub_zero] using ho x
  · change g (-x - (if b i then (1/2 : ℝ) else 0)) =
      -g (x - (if b i then (1/2 : ℝ) else 0))
    rw [hi, ite_eq_left rfl]
    have he : -x - (1/2 : ℝ) = -(x-1/2)-1 := by ring
    rw [he, hp.sub_eq, ho]

lemma periodicRotationNormalScalar_apply (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x) (x : Cover) :
    (periodicRotationNormalScalar g hg hp c N hN hNp).val x =
      g (x 1-c 1)*N x 2-g (x 2-c 2)*N x 1 := by
  rw [periodicRotationNormalScalar_eq]
  simp only [Submodule.coe_sub, Pi.sub_apply, smoothScalarMul, Pi.mul_apply,
    normalComponentScalar_apply]
  rfl

lemma isMinimizerAt_normal_reflection_apply {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i j : Fin 3) (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x : Cover} (hx : quotientMap x ∈ frontier (openRepresentative E)) :
    N (coverCoordinateReflection i x) j = if j=i then -N x j else N x j := by
  have h := congrArg (fun y : Cover => y j)
    (isMinimizerAt_normal_reflection hV hE hm hμ hN hNp hae i hs x hx)
  simp only [coverCoordinateReflection_apply] at h
  split_ifs at h ⊢ <;> linarith

lemma isMinimizerAt_rotation_reflection_odd {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (b : Fin 3 → Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (ho : ∀ x,g (-x) = -g x)
    (i : Fin 3) (hi : i=1 ∨ i=2)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {a : Torus} (ha : a ∈ frontier (openRepresentative E)) :
    (periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp).val
        (representative (coordinateReflection i a)) =
      -(periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp).val
        (representative a) := by
  let f := periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp
  have he : f.val (representative (coordinateReflection i a)) =
      f.val (coverCoordinateReflection i (representative a)) := by
    rw [← quotientMap_representative a, ← quotientMap_coordinateReflection]
    rw [quotientMap_representative]
    exact periodic_representative f.property.2 _
  change f.val _ = -f.val _
  rw [he]
  dsimp only [f]
  rw [periodicRotationNormalScalar_apply, periodicRotationNormalScalar_apply]
  have hx : quotientMap (representative a) ∈ frontier (openRepresentative E) := by
    rwa [quotientMap_representative]
  rw [isMinimizerAt_normal_reflection_apply hV hE hm hμ hN hNp hae i 1 hs hx,
    isMinimizerAt_normal_reflection_apply hV hE hm hμ hN hNp hae i 2 hs hx]
  rcases hi with rfl | rfl
  · simp only [coverCoordinateReflection_apply,
      show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false, odd_periodic_chamberCorner g hp ho]
    ring
  · simp only [coverCoordinateReflection_apply, show (1 : Fin 3) ≠ 2 from by decide,
      ite_true, ite_false, odd_periodic_chamberCorner g hp ho]
    ring

lemma descent_coordinateSine_other_reflection {i j : Fin 3} (hij : i ≠ j) (a : Torus) :
    coordinateSine i (representative (coordinateReflection j a)) =
      coordinateSine i (representative a) := by
  rw [← quotientMap_representative a, ← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine, coverCoordinateReflection_apply, ite_eq_right hij]
  rw [quotientMap_representative]

theorem TrueRadialTube.exists_rotation_zero_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (b : Fin 3 → Bool) {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E (chamberCorner b) r)
    (hs₁ : coordinateReflection 1 ⁻¹' E =ᵐ[torusVolume] E)
    (hs₂ : coordinateReflection 2 ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hNp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ p, let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
        (r p • unitAngle p.2).re * N x 2 - (r p • unitAngle p.2).im * N x 1 = 0 := by
  obtain ⟨μ,N,hN,hNp,g,hg,hp,ho,hμ,ha,he,hnodal⟩ := hr.exists_odd_rotation_nodal_restriction hV hE hm
  let f := periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp
  have hfo (i : Fin 3) (hi : i=1 ∨ i=2)
      (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
      ∀ a ∈ frontier (openRepresentative E), f.val (representative (coordinateReflection i a)) =
        -f.val (representative a) := fun a habd =>
    isMinimizerAt_rotation_reflection_odd hV hE hm hμ hN hNp ha b g hg hp ho i hi hs habd
  have hrS (i : Fin 3) (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
      ∀ a ∈ frontier (openRepresentative E), coordinateReflection i a ∈ frontier (openRepresentative E) := by
    intro a ha
    change a ∈ coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rwa [frontier_reflection_invariant hE i hs]
  have hv := double_reflection_nodal_vanish f (frontier (openRepresentative E))
    (coordinateReflection 1) (coordinateReflection 2) (fun a => coordinateSine 1 (representative a))
    (continuous_periodic_descent (coordinateSine_contDiff 1).continuous (coordinateSine_periodic 1))
    (hrS 1 hs₁) (hrS 2 hs₂) (hfo 1 (Or.inl rfl) hs₁) (hfo 2 (Or.inr rfl) hs₂)
    (descent_coordinateSine_reflection 1)
    (descent_coordinateSine_other_reflection (by decide : (1 : Fin 3) ≠ 2))
    (fun a ha hz => by have h := hfo 1 (Or.inl rfl) hs₁ a ha
                       rw [coordinateReflection_fixed_of_sine_zero 1 hz] at h
                       linarith)
    hnodal
  refine ⟨μ,N,hN,hNp,hμ,ha,?_⟩
  intro p
  let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
  have hx : quotientMap x ∈ frontier (openRepresentative E) := by
    rw [← hr.boundary_range]
    exact ⟨p,rfl⟩
  have h := hv (quotientMap x) hx
  rw [periodic_representative f.property.2] at h
  change f.val x=0 at h
  dsimp only [f] at h
  rw [periodicRotationNormalScalar_apply] at h
  have hx₁ : x 1-chamberCorner b 1=(r p • unitAngle p.2).re := by simp [x]
  have hx₂ : x 2-chamberCorner b 2=(r p • unitAngle p.2).im := by simp [x]
  rw [hx₁,hx₂,(he p).1.eq_of_nhds,(he p).2.eq_of_nhds] at h
  exact h

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.TrueRadialTube.exists_rotation_zero_oai := @OAI.CubicTorus.TrueRadialTube.exists_rotation_zero_oai
