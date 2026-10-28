-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:29:58.822923+00:00
-- url     : https://prove2.me/submissions/646f6680-1e66-483a-8eed-cfaa316b6515

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_axial_boundary_null
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_continuous_axial_sections
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary

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
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus

lemma directionalFlux_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F)
    (i : Fin 3) (g : Cover → ℝ) : directionalFlux E i g = directionalFlux F i g := by
  exact setIntegral_congr_set (liftSet_congr_ae h)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
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
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

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

end CubicTorus.UpperComparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
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

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

end Periodic
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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
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

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x; change (F (x + latticeVector m)) i = (F x) i; rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_variation_of_function i hc hpc
  simpa only [normalFirstVariation, hi, hf] using hH D

end Periodic
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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_denom_pos (v : Cover) :
    0<‖v‖^2+(1-Real.smoothTransition (4*‖v‖^2)) := by
  by_cases h : v=0
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma regularizedNormal_contDiff {R : Cover → Cover}
    (hR : ContDiff ℝ (⊤ : ℕ∞) R) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNormal R) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ‖R x‖^2) := hR.norm_sq ℝ
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ ‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))) :=
    hq.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul hq)))
  exact ((hd.sqrt (fun x ↦ (regularizedNormal_denom_pos _).ne')).inv
    (fun x ↦ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)).ne')).smul hR

lemma regularizedNormal_eq {R : Cover → Cover} {x : Cover} (h : (1/4 : ℝ)≤‖R x‖^2) :
    regularizedNormal R x=‖R x‖⁻¹ • R x := by
  unfold regularizedNormal
  rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,add_zero,
    Real.sqrt_sq (norm_nonneg _)]

lemma regularizedNormal_periodic {R : Cover → Cover}
    (hR : ∀ m x,R (x+latticeVector m)=R x) :
    ∀ m x,regularizedNormal R (x+latticeVector m)=regularizedNormal R x := by
  intro m x
  simp only [regularizedNormal,hR]

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

lemma continuous_periodic_lift {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : Continuous f) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact hf

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_periodic_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) (hm : (∫ t in (0 : ℝ)..1,f t)=0) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧ deriv g=f := by
  let g : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x,f t
  have hd (x : ℝ) : HasDerivAt g (f x) x := (hf.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have he : deriv g=f := funext fun x => (hd x).deriv
  refine ⟨g,contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt,by rw [he]; exact hf⟩,?_,he⟩
  intro x
  change (∫ t in (0 : ℝ)..x+1,f t)=(∫ t in (0 : ℝ)..x,f t)
  rw [hp.intervalIntegral_add_eq_add 0 x (fun a b => hf.continuous.intervalIntegrable a b)]
  simp only [zero_add,hm,add_zero]

lemma periodic_normalized_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      ∀ t,deriv g t=f t-(∫ u in (0 : ℝ)..1,f u) := by
  let c := ∫ u in (0 : ℝ)..1,f u
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun t => f t-c) := hf.sub contDiff_const
  have hpc : Function.Periodic (fun t => f t-c) 1 := fun t => by dsimp only; rw [hp t]
  have hzero : (∫ t in (0 : ℝ)..1,f t-c)=0 := by
    rw [intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _) intervalIntegrable_const]
    simp [c]
  obtain ⟨g,hg,hpg,hdg⟩ := exists_periodic_primitive hfc hpc hzero
  exact ⟨g,hg,hpg,fun t => congrFun hdg t⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fderiv_axial_function (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x v : Cover) :
    fderiv ℝ (fun y : Cover => f (y i)) x v=deriv f (x i)*v i := by
  have hd := (hf (x i)).hasDerivAt.comp_hasFDerivAt x
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  simpa [Function.comp_def] using congrArg (fun L : Cover →L[ℝ] ℝ => L v) hd.fderiv

lemma axial_function_periodic (i : Fin 3) {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa [latticeVector] using hp.int_mul (m i) (x i)

lemma tangentialDivergence_axial (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x n : Cover) :
    tangentialDivergence (fun y : Cover => f (y i) • (EuclideanSpace.single i 1 : Cover)) x n=
      deriv f (x i)*(1-(n i)^2) := by
  have hc : Differentiable ℝ (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiable
  rw [tangentialDivergence_smul_const hc.differentiableAt,fderiv_axial_function i hf]
  congr 1
  simp [tangentPart,PiLp.inner_apply,EuclideanSpace.single,pow_two]

lemma divergence_axial (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Cover) :
    divergence (fun y : Cover => f (y i) • (EuclideanSpace.single i 1 : Cover)) x=deriv f (x i) := by
  have hc : Differentiable ℝ (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiable
  rw [divergence_smul_const hc.differentiableAt,fderiv_axial_function i hf]
  simp [EuclideanSpace.single]

theorem axial_flux_derivative {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ z,deriv f (z.1.1 i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))=
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,deriv f (x i)) := by
  let F : Cover → Cover := fun y => f (y i) • EuclideanSpace.single i 1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hpF : ∀ m x,F (x+latticeVector m)=F x := by
    intro m x
    exact congrArg (fun t : ℝ => t • (EuclideanSpace.single i 1 : Cover))
      (axial_function_periodic i hp m x)
  have he := Periodic.tangent_firstVariation_of_coordinate hH hF hpF
  simpa only [F,tangentialDivergence_axial i (hf.differentiable (by simp)),
    divergence_axial i (hf.differentiable (by simp))] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_axialNormalWeight (i : Fin 3) : Continuous (axialNormalWeight i) :=
  continuous_const.sub (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    continuous_normalUnit).pow 2)

lemma integrable_axialNormalWeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalWeight i) (μ : Measure NormalBundle) :=
  (continuous_axialNormalWeight i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem axial_flux_moment {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ z,f (z.1.1 i)*axialNormalWeight i z ∂(μ : Measure NormalBundle))=
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))+
      (∫ u in (0 : ℝ)..1,f u)*
        ((∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))-
          H*volume.real (fundamentalCube∩quotientMap ⁻¹' E)) := by
  obtain ⟨g,hg,hpg,hdg⟩ := periodic_normalized_primitive hf hp
  have hh := axial_flux_derivative hH i hg hpg
  simp_rw [hdg,sub_mul] at hh
  have hfbase : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
  have hifi : Integrable (fun z : NormalBundle => f (z.1.1 i)*axialNormalWeight i z)
      (μ : Measure NormalBundle) :=
    (hfbase.mul (continuous_axialNormalWeight i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨M,_,hM⟩ := periodic_bounded
    (hf.continuous.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous)
    (axial_function_periodic i hp)
  have hif : Integrable (fun x : Cover => f (x i))
      (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)) :=
    Integrable.of_bound (hf.continuous.comp
      (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous).aestronglyMeasurable M
      (Eventually.of_forall hM)
  change (∫ z,f (z.1.1 i)*axialNormalWeight i z-
    (∫ u in (0 : ℝ)..1,f u)*axialNormalWeight i z ∂(μ : Measure NormalBundle))=
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i)-(∫ u in (0 : ℝ)..1,f u)) at hh
  rw [integral_sub hifi ((integrable_axialNormalWeight μ i).const_mul _),integral_const_mul,
    integral_sub hif (integrable_const _),integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialNormalWeight_nonneg (i : Fin 3) (z : NormalBundle) :
    0≤axialNormalWeight i z := by
  have hb := PiLp.norm_apply_le (x := (z.2 : Cover)) i
  have hn : ‖(z.2 : Cover)‖=1 := z.2.property
  rw [hn,Real.norm_eq_abs] at hb
  dsimp [axialNormalWeight]
  have hs := sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (by norm_num : (0 : ℝ)≤1) |>.mpr hb
  rw [sq_abs,one_pow] at hs
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma scalarMollifier_tendsto : Tendsto (fun n => (scalarMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [scalarMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma scalarMollification_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarMollification f n) :=
  (scalarMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scalarMollifier n).contDiff_normed hf.locallyIntegrable

lemma scalarMollification_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (scalarMollification f n) 1 := by
  intro x
  simp only [scalarMollification,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x+1-y=(x-y)+1 by ring,hp]

lemma scalarMollification_bound {f : ℝ → ℝ} {M : ℝ} (hb : ∀ x,‖f x‖≤M) (n : ℕ) (x : ℝ) :
    ‖scalarMollification f n x‖≤M := by
  rw [scalarMollification,convolution_def]
  calc
    _≤∫ y : ℝ,(scalarMollifier n).normed volume y*M := by
      apply norm_integral_le_of_norm_le ((scalarMollifier n).integrable_normed.mul_const M)
      exact Eventually.of_forall fun y => by
        rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg ((scalarMollifier n).nonneg_normed y)]
        exact mul_le_mul_of_nonneg_left (hb (x-y)) ((scalarMollifier n).nonneg_normed y)
    _=M := by rw [integral_mul_const,(scalarMollifier n).integral_normed,one_mul]

lemma scalarMollification_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n => scalarMollification f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous scalarMollifier_tendsto hf x

theorem circle_measure_ext_smooth {μ ν : Measure (AddCircle (1 : ℝ))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ x,hp.lift x ∂μ)=(∫ x,hp.lift x ∂ν)) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let f : ℝ → ℝ := fun t => g (t : AddCircle (1 : ℝ))
  have hf : Continuous f := g.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hp : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    congr 1
    simp
  obtain ⟨M,hM0,hM⟩ := (isCompact_univ.image g.continuous).isBounded.exists_pos_norm_le
  have hfb (x : ℝ) : ‖f x‖≤M := hM _ ⟨(x : AddCircle (1 : ℝ)),mem_univ _,rfl⟩
  let F (n : ℕ) : AddCircle (1 : ℝ) → ℝ := (scalarMollification_periodic hp n).lift
  have hcF (n : ℕ) : Continuous (F n) := continuous_periodic_lift
    (scalarMollification_periodic hp n) (scalarMollification_contDiff hf n).continuous
  have hbF (n : ℕ) (x : AddCircle (1 : ℝ)) : ‖F n x‖≤M := by
    induction x using QuotientAddGroup.induction_on with | H t =>
      exact scalarMollification_bound hfb n t
  have htF (x : AddCircle (1 : ℝ)) : Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    induction x using QuotientAddGroup.induction_on with | H t =>
      exact scalarMollification_tendsto hf t
  have hlim (ρ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure ρ] :
      Tendsto (fun n => ∫ x,F n x ∂ρ) atTop (𝓝 (∫ x,g x ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (hcF n).aestronglyMeasurable) (integrable_const M)
      (fun n => Eventually.of_forall (hbF n)) (Eventually.of_forall htF)
  apply tendsto_nhds_unique (hlim μ)
  convert hlim ν using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact he _ (scalarMollification_contDiff hf n) (scalarMollification_periodic hp n)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialWeightedHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_continuous_integrable {μ : Measure (AddCircle (1 : ℝ))} [IsFiniteMeasure μ]
    {f : AddCircle (1 : ℝ) → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma continuous_axialBundleHeight (i : Fin 3) : Continuous (axialBundleHeight i) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((PiLp.continuous_apply _ _ i).comp (continuous_subtype_val.comp continuous_fst))

instance axialWeightedHeight_finite (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    IsFiniteMeasure (axialWeightedHeight μ i) := by
  let := isFiniteMeasure_withDensity_ofReal (integrable_axialNormalWeight μ i).hasFiniteIntegral
  unfold axialWeightedHeight
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_axialWeightedHeight (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x,hp.lift x ∂axialWeightedHeight μ i)=
      ∫ z,f (z.1.1 i)*axialNormalWeight i z ∂(μ : Measure NormalBundle) := by
  rw [axialWeightedHeight,integral_map (continuous_axialBundleHeight i).measurable.aemeasurable
    (continuous_periodic_lift hp hf).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_axialNormalWeight i).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (axialNormalWeight_nonneg i z),smul_eq_mul,mul_comm]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem circle_positive_density_of_smooth_moments
    {A : Measure (AddCircle (1 : ℝ))} [IsFiniteMeasure A]
    {q : AddCircle (1 : ℝ) → ℝ} (hq : Continuous q)
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ t,hp.lift t ∂A)=∫ t,q t*hp.lift t) :
    (∀ t,0≤q t) ∧ A=volume.withDensity (fun t => ENNReal.ofReal (q t)) := by
  let p : AddCircle (1 : ℝ) → ℝ := fun t => max (q t) 0
  let n : AddCircle (1 : ℝ) → ℝ := fun t => max (-q t) 0
  have hp : Continuous p := hq.max continuous_const
  have hn : Continuous n := hq.neg.max continuous_const
  have hp0 (t) : 0≤p t := le_max_right _ _
  have hn0 (t) : 0≤n t := le_max_right _ _
  let P : Measure (AddCircle (1 : ℝ)) := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let N : Measure (AddCircle (1 : ℝ)) := volume.withDensity (fun t => ENNReal.ofReal (n t))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    (circle_continuous_integrable hp).hasFiniteIntegral
  let : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal
    (circle_continuous_integrable hn).hasFiniteIntegral
  have hden {w : AddCircle (1 : ℝ) → ℝ} (hw : Continuous w) (hw0 : ∀ t,0≤w t)
      (f : AddCircle (1 : ℝ) → ℝ) :
      (∫ t,f t ∂volume.withDensity (fun t => ENNReal.ofReal (w t)))=∫ t,w t*f t := by
    rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hw0 t),smul_eq_mul]
  have hsplit (t) : q t+n t=p t := by
    rcases le_total (q t) 0 with h|h
    · simp only [n,p,max_eq_left (neg_nonneg.mpr h),max_eq_right h]; ring
    · simp only [n,p,max_eq_right (neg_nonpos.mpr h),max_eq_left h]; ring
  have hbal : A+N=P := by
    apply circle_measure_ext_smooth
    intro f hf hfper
    have hfc := continuous_periodic_lift hfper hf.continuous
    rw [integral_add_measure (circle_continuous_integrable hfc) (circle_continuous_integrable hfc),he f hf hfper]
    change (∫ t,q t*hfper.lift t)+(∫ t,hfper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (n t)))=
      ∫ t,hfper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (p t))
    rw [hden hn hn0,hden hp hp0]
    have hiq : Integrable (fun t => q t*hfper.lift t) := circle_continuous_integrable (hq.mul hfc)
    have hin : Integrable (fun t => n t*hfper.lift t) := circle_continuous_integrable (hn.mul hfc)
    have hia := integral_add hiq hin
    change (∫ t,q t*hfper.lift t+n t*hfper.lift t)=
      (∫ t,q t*hfper.lift t)+(∫ t,n t*hfper.lift t) at hia
    rw [← hia]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by dsimp only; rw [← add_mul,hsplit]
  have hzprod (t) : p t*n t=0 := by
    rcases le_total (q t) 0 with h|h
    · simp [p,max_eq_right h]
    · simp [n,max_eq_right (neg_nonpos.mpr h)]
  have htest := congrArg (fun ρ : Measure (AddCircle (1 : ℝ)) => ∫ t,n t ∂ρ) hbal
  rw [integral_add_measure (circle_continuous_integrable hn) (circle_continuous_integrable hn)] at htest
  change (∫ t,n t ∂A)+(∫ t,n t ∂volume.withDensity (fun t => ENNReal.ofReal (n t)))=
    ∫ t,n t ∂volume.withDensity (fun t => ENNReal.ofReal (p t)) at htest
  rw [hden hn hn0,hden hp hp0] at htest
  simp_rw [hzprod] at htest
  rw [integral_zero] at htest
  have hni : 0≤(∫ t,n t ∂A) := integral_nonneg (fun t => hn0 t)
  have hns : 0≤(∫ t,n t*n t) := integral_nonneg (fun t => mul_self_nonneg (n t))
  have hnzero : (∫ t,n t*n t)=0 := by linarith
  have hnae := (integral_eq_zero_iff_of_nonneg (fun t => mul_self_nonneg (n t))
    (circle_continuous_integrable (hn.mul hn))).mp hnzero
  have hzero : n=fun _ => (0 : ℝ) :=
    Measure.eq_of_ae_eq (hnae.mono fun t ht => mul_self_eq_zero.mp ht) hn continuous_const
  have hq0 (t) : 0≤q t := by
    have htt := congrFun hzero t
    have hh : -q t≤n t := le_max_left _ _
    rw [htt] at hh
    linarith
  refine ⟨hq0,?_⟩
  have hNz : N=0 := by
    dsimp only [N]
    simp only [hzero,ENNReal.ofReal_zero]
    exact withDensity_zero
  have hP : P=volume.withDensity (fun t => ENNReal.ofReal (q t)) := by
    dsimp only [P]
    congr 1
    funext t
    rw [show p t=q t from max_eq_left (hq0 t)]
  simpa only [hNz,add_zero,hP] using hbal

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSplit_measurePreserving (i : Fin 3) : MeasurePreserving (axialSplit i) :=
  UpperComparison.tubeSplit_measurePreserving.comp (coverCoordinatePermute (Equiv.swap 0 i)).measurePreserving

lemma continuous_axialSplit_symm (i : Fin 3) : Continuous (axialSplit i).symm :=
  (coverCoordinatePermute (Equiv.swap 0 i)).symm.continuous.comp UpperComparison.continuous_tubeSplit_symm

lemma measurableSet_transverseSquare : MeasurableSet transverseSquare := by
  change MeasurableSet {y : Plane | ∀ j,y j∈Ico (0 : ℝ) 1}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j =>
    measurableSet_Ico.preimage (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).measurable)

lemma transverseSquare_subset_ball : transverseSquare⊆Metric.closedBall (0 : Plane) 2 := by
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh : ‖y‖^2≤2 := by
    rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
    have h0 := hy 0
    have h1 := hy 1
    simp only [Real.norm_eq_abs,sq_abs]
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  nlinarith [norm_nonneg y]

lemma volume_transverseSquare_lt_top : volume transverseSquare<⊤ :=
  (measure_mono transverseSquare_subset_ball).trans_lt measure_closedBall_lt_top

lemma mem_axialSplit_cube (i : Fin 3) (x : Cover) :
    x∈fundamentalCube ↔ axialSplit i x∈Ico (0 : ℝ) 1 ×ˢ transverseSquare := by
  let y := coverCoordinatePermute (Equiv.swap 0 i) x
  have he : x∈fundamentalCube ↔ y∈fundamentalCube := by
    constructor
    · intro hx j
      exact hx ((Equiv.swap 0 i) j)
    · intro hy j
      have hh := hy ((Equiv.swap 0 i) j)
      simpa [y] using hh
  rw [he]
  change (∀ j,0≤y j ∧ y j<1) ↔ (0≤y 0 ∧ y 0<1) ∧ ∀ j : Fin 2,0≤y j.succ ∧ y j.succ<1
  constructor
  · intro hy
    exact ⟨hy 0,fun j => hy j.succ⟩
  · rintro ⟨h0,hs⟩ j
    exact Fin.cases h0 hs j

lemma axialSplit_preimage_cube (i : Fin 3) :
    axialSplit i ⁻¹' (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=fundamentalCube := by
  ext x
  exact (mem_axialSplit_cube i x).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_axialSquare : volume transverseSquare=1 := by
  have he := (axialSplit_measurePreserving 0).measure_preimage
    ((measurableSet_Ico (a := (0 : ℝ)) (b := 1)).prod measurableSet_transverseSquare).nullMeasurableSet
  rw [axialSplit_preimage_cube,volume_fundamentalCube,Measure.volume_eq_prod,
    Measure.prod_prod,Real.volume_Ico] at he
  simpa using he.symm

lemma volume_axialRectangle : volume (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=1 := by
  rw [Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ico,volume_axialSquare]
  norm_num

lemma axial_section_inner {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) (t c : ℝ) :
    (∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      axialSectionArea E i t*c := by
  let B : Set Plane := (fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E
  have hB : MeasurableSet B := hE.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he : (fun y => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      B.indicator (fun _ => c) := by
    funext y
    by_cases hy : y∈B
    · simp only [indicator_of_mem hy]
      change quotientMap ((axialSplit i).symm (t,y))∈E at hy
      simp only [characteristic,indicator_of_mem hy,one_mul]
    · simp only [indicator_of_notMem hy]
      change quotientMap ((axialSplit i).symm (t,y))∉E at hy
      simp only [characteristic,indicator_of_notMem hy,zero_mul]
  rw [he,setIntegral_indicator hB,integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  rfl

lemma integrable_axialIndicator {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    IntegrableOn (fun z : ℝ × Plane => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1)
      (Ico (0 : ℝ) 1 ×ˢ transverseSquare) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous) (axial_function_periodic i hp)
  apply IntegrableOn.of_bound (by rw [volume_axialRectangle]; simp)
    (((measurable_characteristic hE).comp (measurable_quotientMap.comp (axialSplit i).symm.measurable)).mul
      (hf.measurable.comp measurable_fst)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro z
  have hb : ‖f z.1‖≤M := by
    have hh := hM ((axialSplit i).symm z)
    change ‖f ((axialSplit i).symm z i)‖≤M at hh
    simpa only [axialSplit_symm_axis] using hh
  change ‖characteristic E (quotientMap ((axialSplit i).symm z))*f z.1‖≤M
  by_cases hz : quotientMap ((axialSplit i).symm z)∈E
  · simpa only [characteristic,indicator_of_mem hz,one_mul] using hb
  · simp only [characteristic,indicator_of_notMem hz,zero_mul,norm_zero]
    exact hM0

theorem axial_section_fubini {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      ∫ t in Ico (0 : ℝ) 1,axialSectionArea E i t*f t := by
  let g : ℝ × Plane → ℝ := fun z => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1
  have he := (axialSplit_measurePreserving i).setIntegral_preimage_emb
    (axialSplit i).measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ transverseSquare)
  rw [axialSplit_preimage_cube] at he
  have hleft : (fun x : Cover => g (axialSplit i x))=
      (quotientMap ⁻¹' E).indicator (fun x => f (x i)) := by
    funext x
    dsimp [g]
    rw [(axialSplit i).symm_apply_apply,axialSplit_fst]
    by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]
  rw [hleft,setIntegral_indicator (hE.preimage measurable_quotientMap)] at he
  rw [he]
  have hi := integrable_axialIndicator hE i hf hp
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact axial_section_inner hE i t (f t)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialFluxDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma integral_axialCircleArea_mul {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ t,axialCircleArea E i t*hp.lift t)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i) := by
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add,axialCircleArea_coe,Function.Periodic.lift_coe]
  rw [axial_section_fubini hE i hf hp,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    integral_Ico_eq_integral_Ioc]

theorem axialWeightedHeight_density {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (hc : Continuous (axialSectionArea E i)) :
    (∀ t : ℝ,0≤(μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)) ∧
    axialWeightedHeight μ i=volume.withDensity (fun t => ENNReal.ofReal
      ((μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V))) := by
  have hvc : Continuous (axialCircleArea E i) :=
    continuous_periodic_lift (axialSectionArea_periodic E i) hc
  let C := (μ.mass : ℝ)*axialFluxWeight μ i
  have hC : C=(∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle)) := by
    by_cases hm : (μ.mass : ℝ)=0
    · have hz : μ=0 := (FiniteMeasure.mass_zero_iff μ).mp (NNReal.coe_eq_zero.mp hm)
      simp [C,hz,axialFluxWeight]
    · dsimp [C,axialFluxWeight]
      field_simp
  obtain ⟨hpos,hdens⟩ := circle_positive_density_of_smooth_moments
    (A := axialWeightedHeight μ i) (q := fun t => C+H*(axialCircleArea E i t-V))
    (continuous_const.add (continuous_const.mul (hvc.sub continuous_const))) (by
      intro f hf hp
      rw [integral_axialWeightedHeight μ i hf.continuous hp]
      have he := axial_flux_moment hH i hf hp
      have hvol' : volume.real (fundamentalCube∩quotientMap ⁻¹' E)=V := by
        rw [← realVolume_lift hE,hvol]
      rw [hvol',← hC] at he
      have hfi : Integrable hp.lift := circle_continuous_integrable (continuous_periodic_lift hp hf.continuous)
      have hvi : Integrable (fun t => axialCircleArea E i t*hp.lift t) :=
        circle_continuous_integrable (hvc.mul (continuous_periodic_lift hp hf.continuous))
      have hfun : (fun t => (C+H*(axialCircleArea E i t-V))*hp.lift t)=
          (fun t => H*(axialCircleArea E i t*hp.lift t)+(C-H*V)*hp.lift t) := by
        funext t
        ring
      rw [hfun,integral_add (hvi.const_mul H) (hfi.const_mul (C-H*V)),
        integral_const_mul,integral_const_mul,integral_axialCircleArea_mul hE i hf.continuous hp]
      have hcircle := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 hp.lift
      simp only [zero_add,Function.Periodic.lift_coe] at hcircle
      rw [← hcircle]
      linarith [he])
  exact ⟨fun t => by simpa only [axialCircleArea_coe,C] using hpos (t : AddCircle (1 : ℝ)),hdens⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSectionIntegral_periodic (E : Set Torus) (i : Fin 3) {g : Cover → ℝ}
    (hp : ∀ m x,g (x+latticeVector m)=g x) : Function.Periodic (axialSectionIntegral E i g) 1 := by
  intro t
  apply setIntegral_congr_fun measurableSet_transverseSquare
  intro y hy
  have he : EuclideanSpace.single i (1 : ℝ)=latticeVector (Pi.single i (1 : ℤ)) := by
    ext j
    simp [latticeVector,Pi.single_apply]
  dsimp only
  rw [axialSplit_symm_axis_line i (t+1) t y,show t+1-t=1 by ring,one_smul,he,
    hp,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma continuous_axialSectionIntegral_of_boundary_null {E : Set Torus}
    (hE : MeasurableSet E) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    Continuous (axialSectionIntegral E i g) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  rw [continuous_iff_continuousAt]
  intro t
  apply continuousAt_of_dominated (bound := fun _ : Plane => M)
  · apply Eventually.of_forall
    intro u
    exact (((measurable_characteristic hE).comp (measurable_quotientMap.comp
      ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).mul
      (hg.measurable.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun u => Eventually.of_forall fun y => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hM ((axialSplit i).symm (u,y)))
  · exact integrableOn_const volume_transverseSquare_lt_top.ne
  · have hnull : ∀ᵐ y : Plane,quotientMap ((axialSplit i).symm (t,y))∉frontier E := by
      rw [ae_iff]
      simpa only [not_not] using hz t
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    have hc : ContinuousAt (characteristic E) (quotientMap ((axialSplit i).symm (t,y))) :=
      (continuousOn_const : ContinuousOn (fun _ : Torus => (1 : ℝ)) (interior E)).continuousAt_indicator hy
    have hx : ContinuousAt (fun u : ℝ => (axialSplit i).symm (u,y)) t :=
      ((continuous_axialSplit_symm i).comp (continuous_id.prodMk continuous_const)).continuousAt
    have hq : ContinuousAt (fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) t :=
      ContinuousAt.comp (f := fun u : ℝ => (axialSplit i).symm (u,y)) continuous_quotientMap.continuousAt hx
    exact (ContinuousAt.comp (f := fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) hc hq).mul
      (ContinuousAt.comp (f := fun u : ℝ => (axialSplit i).symm (u,y)) hg.continuousAt hx)

lemma integrable_axialWeightedIndicator {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    IntegrableOn (fun z : ℝ × Plane => characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z))
      (Ico (0 : ℝ) 1 ×ˢ transverseSquare) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  apply IntegrableOn.of_bound (by rw [volume_axialRectangle]; simp)
    (((measurable_characteristic hE).comp (measurable_quotientMap.comp (axialSplit i).symm.measurable)).mul
      (hg.measurable.comp (axialSplit i).symm.measurable)).aestronglyMeasurable M
  exact Eventually.of_forall fun z => by
    change ‖characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z)‖≤M
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM ((axialSplit i).symm z))

theorem axial_weighted_section_fubini {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,g x)=
      ∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i g t := by
  let f : ℝ × Plane → ℝ := fun z => characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z)
  have he := (axialSplit_measurePreserving i).setIntegral_preimage_emb
    (axialSplit i).measurableEmbedding f (Ico (0 : ℝ) 1 ×ˢ transverseSquare)
  rw [axialSplit_preimage_cube] at he
  have hleft : (fun x : Cover => f (axialSplit i x))=(quotientMap ⁻¹' E).indicator g := by
    funext x
    dsimp [f]
    rw [(axialSplit i).symm_apply_apply]
    by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]
  rw [hleft,setIntegral_indicator (hE.preimage measurable_quotientMap)] at he
  rw [he]
  have hi := integrable_axialWeightedIndicator hE i hg hp
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  rfl

lemma axialSectionIntegral_mul_height (E : Set Torus) (i : Fin 3) (g : Cover → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    axialSectionIntegral E i (fun x => g x*f (x i)) t=axialSectionIntegral E i g t*f t := by
  dsimp only [axialSectionIntegral]
  simp only [axialSplit_symm_axis,← mul_assoc]
  exact integral_mul_const _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_height_tangent {F : Cover → Cover} (hF : AdmissibleField F)
    (i : Fin 3) (ht : ∀ x,F x i=0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Cover) :
    divergence (fun y => f (y i) • F y) x=divergence F x*f (x i) := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  rw [divergence_smul_function (hfa.differentiable (by simp) x) (hF.1.differentiable (by simp) x),
    inner_gradient_left,fderiv_axial_function i (hf.differentiable (by simp)),ht,mul_zero,add_zero,mul_comm]

lemma axial_slice_flux_moment {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (divergence F) t*f t)=
      ∫ z,f (z.1.1 i)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  have he := normalMeasure_weighted_flux hμ hfa (axial_function_periodic i hp) hF
  simp_rw [divergence_height_tangent hF i ht hf] at he
  have hgp : ∀ m x,divergence F (x+latticeVector m)*f ((x+latticeVector m) i)=divergence F x*f (x i) := by
    intro m x
    rw [divergence_periodic hF.2.1,axial_function_periodic i hp]
  have hh := axial_weighted_section_fubini hE i ((continuous_divergence hF.1).mul hfa.continuous) hgp
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x*f (x i))=
    ∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (fun x => divergence F x*f (x i)) t at hh
  rw [hh] at he
  simpa only [axialSectionIntegral_mul_height] using he.symm

lemma unit_normal_tangent_quadratic_bound {u v : Cover} (hu : ‖u‖=1) (hv : ‖v‖≤1)
    (i : Fin 3) (ht : v i=0) : ⟪u,v⟫≤1-(u i)^2/2 := by
  have hp := PiLp.norm_apply_le (x := u-v) i
  simp only [PiLp.sub_apply,ht,sub_zero,Real.norm_eq_abs] at hp
  have hps : (u i)^2≤‖u-v‖^2 := by
    exact (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (u i)) (norm_nonneg (u-v))).mpr hp)
  rw [norm_sub_sq_real,hu,one_pow] at hps
  have hvs : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
  linarith

theorem axial_slice_flux_quadratic_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) (hf0 : ∀ t,0≤f t) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (divergence F) t*f t)≤
      (∫ z,axialNormalWeight i z*f (z.1.1 i) ∂(μ : Measure NormalBundle))+
      (∫ z,((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle)) := by
  rw [axial_slice_flux_moment hE hμ hF i ht hf hp]
  have hcF : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp (continuous_subtype_val.comp continuous_fst))
  have hcn : Continuous (fun z : NormalBundle => ((z.2 : Cover) i)^2/2) :=
    ((((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2).div_const 2)
  have hi1 : Integrable (fun z => axialNormalWeight i z*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    ((continuous_axialNormalWeight i).mul hcF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun z => ((z.2 : Cover) i)^2/2*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    (hcn.mul hcF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hia := integral_add hi1 hi2
  change (∫ z,axialNormalWeight i z*f (z.1.1 i)+((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle))=_ at hia
  rw [← hia]
  apply integral_mono
    ((hcF.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hi1.add hi2)
  intro z
  have hb := unit_normal_tangent_quadratic_bound z.2.property (hF.2.2 z.1) i (ht z.1)
  have hh := mul_le_mul_of_nonneg_right hb (hf0 (z.1.1 i))
  change f (z.1.1 i)*⟪(z.2 : Cover),F z.1⟫≤_
  dsimp only [axialNormalWeight,Pi.add_apply]
  nlinarith [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma axial_density_moment {V : ℝ} {E : Set Torus} (hE : MeasurableSet E)
    (hvol : torusVolume.real E=V) {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (axialSectionArea E i))
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t in (0 : ℝ)..1,((μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V))*f t)=
      ∫ z,axialNormalWeight i z*f (z.1.1 i) ∂(μ : Measure NormalBundle) := by
  obtain ⟨hq0,hd⟩ := axialWeightedHeight_density hE hvol hH i hc
  have he := integral_axialWeightedHeight μ i hf.continuous hp
  have hqc : Continuous (fun t : AddCircle (1 : ℝ) =>
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V)) :=
    continuous_const.add (continuous_const.mul
      ((continuous_periodic_lift (axialSectionArea_periodic E i) hc).sub continuous_const))
  rw [hd,integral_withDensity_eq_integral_toReal_smul hqc.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at he
  have hq0' (t : AddCircle (1 : ℝ)) :
      0≤(μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V) := by
    obtain ⟨u,rfl⟩ := Quotient.exists_rep t
    simpa only [axialCircleArea_coe] using hq0 u
  simp_rw [ENNReal.toReal_ofReal (hq0' _),smul_eq_mul] at he
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at he
  simp only [zero_add,axialCircleArea_coe,Function.Periodic.lift_coe] at he
  exact he.trans (integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_smooth_lipschitz {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∃ K : ℝ≥0,LipschitzWith K F := by
  obtain ⟨M,hM,hb⟩ := periodic_bounded (hF.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨M,hM⟩,lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp)) hb⟩

lemma half_abs_sin_bound {t : ℝ} (ht : |t|≤1/2) :
    2*|t|≤|Real.sin (Real.pi*t)| := by
  have hh := Real.le_sin_mul (show 0≤2*|t| by positivity) (show 2*|t|≤1 by linarith)
  have he : Real.pi/2*(2*|t|)=Real.pi*|t| := by ring
  rw [he] at hh
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h] at hh ⊢
    exact hh.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hh ⊢
    rw [show Real.pi * -t = -(Real.pi*t) by ring,Real.sin_neg] at hh
    exact hh.trans (neg_le_abs _)

theorem isMinimizerAt_normal_reflection_rate {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ K : ℝ≥0,∀ (i : Fin 3) (b : Bool) (x : Cover),x∈closedFundamentalCube →
      quotientMap x∈frontier (openRepresentative E) →
      |N x i|≤(K : ℝ)*|Real.sin (Real.pi*(x i-(if b then 1/2 else 0)))| := by
  obtain ⟨K,hK⟩ := periodic_smooth_lipschitz hN hp
  refine ⟨K,?_⟩
  intro i b x hx hbd
  have hxi : ∀ j : Fin 3,0≤x j ∧ x j≤1 := by
    obtain ⟨y,hy,rfl⟩ := hx
    exact fun j => ⟨hy.1 j,hy.2 j⟩
  have hk (k : ℤ) : |N x i|≤(K : ℝ)*|x i-(k : ℝ)/2| := by
    let y := coverCoordinateReflection i x+latticeVector (Pi.single i k)
    have hNi : N y i= -N x i := by
      rw [show N y=N (coverCoordinateReflection i x) from hp _ _]
      have he := congrArg (fun z : Cover => z i) (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hbd)
      simp only [coverCoordinateReflection_apply,ite_true] at he
      linarith
    have hd := hK.dist_le_mul x y
    have hl : 2*|N x i|≤dist (N x) (N y) := by
      have hh := PiLp.norm_apply_le (x := N x-N y) i
      simpa only [PiLp.sub_apply,hNi,sub_neg_eq_add,← two_mul,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ)≤2),dist_eq_norm] using hh
    have he : x-y=(2*(x i-(k : ℝ)/2)) • EuclideanSpace.single i 1 := by
      ext j
      by_cases hj : j=i
      · subst j
        simp [y,coverCoordinateReflection_apply,latticeVector,Pi.single_apply]; ring
      · simp [y,coverCoordinateReflection_apply,latticeVector,Pi.single_apply,hj]
    have hd' : dist x y=2*|x i-(k : ℝ)/2| := by
      rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      simp
    rw [hd'] at hd
    nlinarith [hl.trans hd]
  cases b
  · simp only [Bool.false_eq_true,ite_false,sub_zero]
    by_cases ht : x i≤1/2
    · have hsin := half_abs_sin_bound (t := x i) (by rw [abs_of_nonneg (hxi i).1]; exact ht)
      have hh := hk 0
      simp only [Int.cast_zero,zero_div,sub_zero] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i)]) K.coe_nonneg)
    · have hsin := half_abs_sin_bound (t := x i-1) (by
        rw [abs_of_nonpos (by linarith [(hxi i).2])]
        linarith)
      have he : Real.sin (Real.pi*(x i-1))= -Real.sin (Real.pi*x i) := by
        rw [mul_sub,mul_one,Real.sin_sub_pi]
      rw [he,abs_neg] at hsin
      have hh := hk 2
      norm_num at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i-1)]) K.coe_nonneg)
  · simp only [ite_true]
    have hsin := half_abs_sin_bound (t := x i-1/2) (by
      rw [abs_le]
      constructor <;> linarith [(hxi i).1,(hxi i).2])
    have hh := hk 1
    norm_num at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i-1/2)]) K.coe_nonneg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma abs_sin_height_periodic (a : ℝ) :
    Function.Periodic (fun t : ℝ => |Real.sin (Real.pi*(t-a))|) 1 := by
  intro t
  dsimp only
  rw [show Real.pi*(t+1-a)=Real.pi*(t-a)+Real.pi by ring,Real.sin_add_pi,abs_neg]

theorem circle_quadratic_contact {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h 1) (a : ℝ) {M : ℝ} (hM : 0≤M)
    (hmom : ∀ (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → Function.Periodic f 1 →
      (∀ t,0≤f t) → (∀ t,f t≤1) → ∀ δ : ℝ,0≤δ →
      (∀ t,f t≠0 → |Real.sin (Real.pi*(t-a))|≤δ) →
      (∫ t in (0 : ℝ)..1,h t*f t)≤M*δ^2) : h a≤0 := by
  by_contra ha
  have ha : 0<h a := lt_of_not_ge ha
  let c := h a/2
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hca : c<h a := by dsimp [c]; linarith
  have hv : ∀ᶠ t in 𝓝 a,c<h t := hc.continuousAt.eventually (eventually_gt_nhds hca)
  obtain ⟨r,hr,hlocal⟩ := Metric.mem_nhds_iff.mp hv
  let B := M*Real.pi^2+1
  have hB : 0<B := by dsimp [B]; positivity
  let ε := min (r/2) (min (1/4) (c/(2*B)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεr : ε < r := (min_le_left _ _).trans_lt (by linarith)
  have hεh : ε<1/2 := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num))
  have hεB : ε ≤ c/(2*B) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : M*Real.pi^2*ε < c := by
    have hmul := (le_div_iff₀ (by positivity : 0<2*B)).mp hεB
    dsimp [B] at hmul
    nlinarith [mul_nonneg hM (sq_nonneg Real.pi)]
  let b : ContDiffBump a :=
    { rIn := ε/2
      rOut := ε
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hbs : tsupport b⊆Ioo (a-1/2) (a+1/2) := by
    rw [b.tsupport_eq]
    intro t ht
    have hd : |t-a|≤ε := by simpa only [Metric.mem_closedBall,Real.dist_eq,b] using ht
    obtain ⟨hl,hu⟩ := abs_le.mp hd
    constructor <;> linarith
  let f : ℝ → ℝ := circlePeriodize b
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := circlePeriodize_contDiff b.contDiff b.hasCompactSupport
  have hfp : Function.Periodic f 1 := circlePeriodize_periodic b
  have hfb (t) : 0≤f t ∧ f t≤1 := circlePeriodize_unit_bounds hbs (fun _ => ⟨b.nonneg,b.le_one⟩) t
  have hsupport (t) (ht : f t≠0) : ∃ n : ℤ,|t+n-a|<ε := by
    by_contra hn
    have hz : ∀ n : ℤ,b (t+n)=0 := by
      intro n
      apply b.zero_of_le_dist
      have hn' : ¬|t+n-a|<ε := fun h => hn ⟨n,h⟩
      simpa only [Real.dist_eq,b] using le_of_not_gt hn'
    apply ht
    show (∑' n : ℤ,b (t+n))=0
    simp only [hz,tsum_zero]
  have hsin (t) (ht : f t≠0) : |Real.sin (Real.pi*(t-a))|≤Real.pi*ε := by
    obtain ⟨n,hn⟩ := hsupport t ht
    have he := (abs_sin_height_periodic a).int_mul n t
    simp only [mul_one] at he
    rw [← he]
    exact Real.abs_sin_le_abs.trans (by rw [abs_mul,abs_of_pos Real.pi_pos]; exact mul_le_mul_of_nonneg_left hn.le Real.pi_pos.le)
  have hprod (t) : c*f t≤h t*f t := by
    by_cases ht : f t=0
    · simp [ht]
    · obtain ⟨n,hn⟩ := hsupport t ht
      have hnear : t+n∈Metric.ball a r := by rw [Metric.mem_ball,Real.dist_eq]; exact hn.trans hεr
      have hh : c<h (t+n) := hlocal hnear
      have he := hp.int_mul n t
      simp only [mul_one] at he
      rw [he] at hh
      exact mul_le_mul_of_nonneg_right hh.le (hfb t).1
  have heq (t) (ht : t∈Icc (a-1/2) (a+1/2)) : f t=b t :=
    (circlePeriodize_eventuallyEq b.hasCompactSupport hbs ht).eq_of_nhds
  have hint : ε≤∫ t in (0 : ℝ)..1,f t := by
    have hshift := hfp.intervalIntegral_add_eq 0 (a-1/2)
    simp only [zero_add] at hshift
    rw [show a-1/2+1=a+1/2 by ring] at hshift
    rw [hshift]
    have hbint : (∫ t in a-1/2..a+1/2,f t)=∫ t in a-1/2..a+1/2,b t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : a-1/2≤a+1/2)] at ht
      exact heq t ht
    rw [hbint]
    have hine : (∫ t in a-ε/2..a+ε/2,b t)=ε := by
      have he := intervalIntegral.integral_congr (μ := volume) (a := a-ε/2) (b := a+ε/2) (f := (b : ℝ → ℝ)) (g := fun _ => (1 : ℝ)) (by
        intro t ht
        rw [uIcc_of_le (by linarith : a-ε/2≤a+ε/2)] at ht
        apply b.one_of_mem_closedBall
        rw [Metric.mem_closedBall,Real.dist_eq]
        change |t-a|≤ε/2
        rw [abs_le]
        constructor <;> linarith [ht.1,ht.2])
      rw [he,intervalIntegral.integral_const]
      simp only [smul_eq_mul,mul_one]
      ring
    rw [← hine]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun _ => b.nonneg) (b.continuous.intervalIntegrable _ _)
  have hlo : c*ε≤∫ t in (0 : ℝ)..1,h t*f t := by
    apply (mul_le_mul_of_nonneg_left hint hc0.le).trans
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono (by norm_num)
      ((continuous_const.mul hfc.continuous).intervalIntegrable _ _)
      ((hc.mul hfc.continuous).intervalIntegrable _ _) hprod
  have hupper := hmom f hfc hfp (fun t => (hfb t).1) (fun t => (hfb t).2)
    (Real.pi*ε) (by positivity) hsin
  have hbig : c≤M*Real.pi^2*ε := by nlinarith [hlo.trans hupper]
  exact (not_le_of_gt hsmall) hbig

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_slice_endpoint_bound {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    (hc : Continuous (axialSectionArea E i))
    (hcf : Continuous (axialSectionIntegral E i (divergence F)))
    (a : ℝ) {K : ℝ} (hK : 0≤K)
    (hR : ∀ᵐ z ∂(μ : Measure NormalBundle),|((z.2 : Cover) i)|≤K*|Real.sin (Real.pi*(z.1.1 i-a))|) :
    axialSectionIntegral E i (divergence F) a≤
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i a-V) := by
  let p := axialSectionIntegral E i (divergence F)
  let q := fun t => (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)
  have hqc : Continuous q := continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  have hpp : Function.Periodic p 1 := axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)
  have hqp : Function.Periodic q 1 := by
    intro t
    dsimp [q]
    rw [axialSectionArea_periodic E i]
  suffices h : p a-q a≤0 by dsimp [p,q] at h; linarith
  apply circle_quadratic_contact (hcf.sub hqc) (hpp.sub hqp) a
    (M := K^2/2*(μ.mass : ℝ)) (by positivity)
  intro f hf hp hf0 hf1 δ hδ hδsupp
  have hb := axial_slice_flux_quadratic_bound hE hμ hF i ht hf hp hf0
  have hden := axial_density_moment hE hvol hH i hc hf hp
  have hic : (∫ t in Ico (0 : ℝ) 1,p t*f t)=∫ t in (0 : ℝ)..1,p t*f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Ico_eq_integral_Ioc]
  change (∫ t in Ico (0 : ℝ) 1,p t*f t)≤_ at hb
  rw [hic] at hb
  have hsub : (∫ t in (0 : ℝ)..1,(p t-q t)*f t)=
      (∫ t in (0 : ℝ)..1,p t*f t)-(∫ t in (0 : ℝ)..1,q t*f t) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub ((hcf.mul hf.continuous).intervalIntegrable _ _)
      ((hqc.mul hf.continuous).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..1,(p t-q t)*f t)≤_
  rw [hsub]
  change (∫ t in (0 : ℝ)..1,q t*f t)=_ at hden
  rw [hden]
  apply (sub_le_iff_le_add'.mpr hb).trans
  have hcn : Continuous (fun z : NormalBundle => ((z.2 : Cover) i)^2/2*f (z.1.1 i)) :=
    ((((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2).div_const 2).mul
      (hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_fst)))
  calc
    (∫ z,((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle))≤
        ∫ _ : NormalBundle,K^2*δ^2/2 ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      filter_upwards [hR] with z hz
      by_cases hzero : f (z.1.1 i)=0
      · simp only [hzero,mul_zero]
        positivity
      · have hn := hz.trans (mul_le_mul_of_nonneg_left (hδsupp _ hzero) hK)
        have hsq : ((z.2 : Cover) i)^2≤K^2*δ^2 := by
          have hh := (sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (mul_nonneg hK hδ)).mpr hn
          simpa only [sq_abs,mul_pow] using hh
        calc
          _≤((z.2 : Cover) i)^2/2*1 := mul_le_mul_of_nonneg_left (hf1 _) (by positivity)
          _≤K^2*δ^2/2 := by nlinarith
    _=K^2/2*(μ.mass : ℝ)*δ^2 := by
      simp only [integral_const,smul_eq_mul,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
      ring

theorem isMinimizerAt_axial_slice_endpoint_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0) (b : Bool) :
    axialSectionIntegral (openRepresentative E) i (divergence F) (if b then 1/2 else 0)≤
      (μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hHo : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux (openRepresentative E) D.coordinate D.function := by
    intro D
    rw [directionalFlux_congr_ae hae,hH]
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  have hcf := continuous_axialSectionIntegral_of_boundary_null
    (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)
    (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  obtain ⟨K,hK⟩ := isMinimizerAt_normal_reflection_rate hV hE hm hμ hN hp ha hs
  apply axial_slice_endpoint_bound (isOpen_openRepresentative E).measurableSet hvol hμo hHo hF i ht hc hcf
    (if b then 1/2 else 0) K.coe_nonneg
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo,ha] with z hz hzn
  have hh := hK i b z.1 z.1.property hz
  rw [hzn] at hh
  exact hh

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialNormalCalibration
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

lemma regularizedNormal_norm_le (R : Cover → Cover) (x : Cover) : ‖regularizedNormal R x‖≤1 := by
  rw [regularizedNormal,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _))),
    inv_mul_le_iff₀ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)),mul_one]
  apply Real.le_sqrt_of_sq_le
  linarith [Real.smoothTransition.le_one (4*‖R x‖^2)]

lemma axialTangentPart_axis (i : Fin 3) (u : Cover) : axialTangentPart i u i=0 := by
  simp [axialTangentPart]

lemma axialTangentPart_norm_sq (i : Fin 3) (u : Cover) :
    ‖axialTangentPart i u‖^2=‖u‖^2-(u i)^2 := by
  rw [axialTangentPart,norm_sub_sq_real,norm_smul,real_inner_smul_right]
  simp only [PiLp.norm_single,Real.norm_eq_abs,abs_one,mul_one,
    EuclideanSpace.inner_single_right,conj_trivial]
  rw [sq_abs]
  ring

lemma inner_axialTangentPart (i : Fin 3) (u : Cover) :
    ⟪u,axialTangentPart i u⟫=‖u‖^2-(u i)^2 := by
  rw [axialTangentPart,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_smul_right]
  simp only [EuclideanSpace.inner_single_right,conj_trivial]
  ring

lemma axialTangentPart_contDiff {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => axialTangentPart i (N x)) :=
  hN.sub (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hN).smul contDiff_const)

lemma axialNormalCalibration_admissible {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) :
    AdmissibleField (axialNormalCalibration N i) := by
  refine ⟨regularizedNormal_contDiff (axialTangentPart_contDiff hN i),?_,?_⟩
  · apply regularizedNormal_periodic
    intro m x
    rw [hp]
  · exact regularizedNormal_norm_le _

lemma axialNormalCalibration_axis (N : Cover → Cover) (i : Fin 3) (x : Cover) :
    axialNormalCalibration N i x i=0 := by
  simp only [axialNormalCalibration,regularizedNormal,PiLp.smul_apply,smul_eq_mul,axialTangentPart_axis,mul_zero]

lemma axialNormalCalibration_quadratic_lower (N : Cover → Cover) (i : Fin 3) (x : Cover)
    (hu : ‖N x‖=1) :
    1-(N x i)^2-⟪N x,axialNormalCalibration N i x⟫≤(N x i)^2 := by
  let w := 1-(N x i)^2
  have hw : ‖axialTangentPart i (N x)‖^2=w := by rw [axialTangentPart_norm_sq,hu,one_pow]
  have hw0 : 0≤w := by rw [← hw]; positivity
  have hw1 : w≤1 := by dsimp [w]; linarith [sq_nonneg (N x i)]
  have hin : ⟪N x,axialTangentPart i (N x)⟫=w := by rw [inner_axialTangentPart,hu,one_pow]
  have hf0 : 0≤⟪N x,axialNormalCalibration N i x⟫ := by
    rw [axialNormalCalibration,regularizedNormal,real_inner_smul_right,hin]
    positivity
  by_cases hh : 1/4≤w
  · have hnorm0 : 0<‖axialTangentPart i (N x)‖ := by
      have hpos : 0<‖axialTangentPart i (N x)‖^2 := by rw [hw]; linarith
      exact lt_of_le_of_ne (norm_nonneg _) (fun he => by rw [← he] at hpos; norm_num at hpos)
    have hnorm1 : ‖axialTangentPart i (N x)‖≤1 := by nlinarith [norm_nonneg (axialTangentPart i (N x))]
    have he : ⟪N x,axialNormalCalibration N i x⟫=
        w/‖axialTangentPart i (N x)‖ := by
      rw [axialNormalCalibration,regularizedNormal_eq (by rw [hw]; exact hh),real_inner_smul_right,hin]
      ring
    have hge : w≤⟪N x,axialNormalCalibration N i x⟫ := by
      rw [he,le_div_iff₀ hnorm0]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm1 hw0
    change w-⟪N x,axialNormalCalibration N i x⟫≤_
    linarith [sq_nonneg (N x i)]
  · change w-⟪N x,axialNormalCalibration N i x⟫≤_
    dsimp only [w] at hh ⊢
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_slice_endpoint_calibration {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i : Fin 3) (hc : Continuous (axialSectionArea E i))
    (hcf : Continuous (axialSectionIntegral E i (divergence (axialNormalCalibration N i))))
    (a : ℝ) {K : ℝ} (hK : 0≤K)
    (hR : ∀ᵐ z ∂(μ : Measure NormalBundle),|((z.2 : Cover) i)|≤K*|Real.sin (Real.pi*(z.1.1 i-a))|) :
    axialSectionIntegral E i (divergence (axialNormalCalibration N i)) a=
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i a-V) := by
  let F := axialNormalCalibration N i
  have hF : AdmissibleField F := axialNormalCalibration_admissible hN hp i
  have ht : ∀ x,F x i=0 := axialNormalCalibration_axis N i
  apply le_antisymm (axial_slice_endpoint_bound hE hvol hμ hH hF i ht hc hcf a hK hR)
  let p := axialSectionIntegral E i (divergence F)
  let q := fun t => (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)
  have hqc : Continuous q := continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  have hpp : Function.Periodic p 1 := axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)
  have hqp : Function.Periodic q 1 := by
    intro t
    dsimp [q]
    rw [axialSectionArea_periodic E i]
  suffices h : q a-p a≤0 by dsimp [p,q,F] at h; linarith
  apply circle_quadratic_contact (hqc.sub hcf) (hqp.sub hpp) a
    (M := K^2*(μ.mass : ℝ)) (by positivity)
  intro f hf hfp hf0 hf1 δ hδ hδsupp
  have hden := axial_density_moment hE hvol hH i hc hf hfp
  have hflux := axial_slice_flux_moment hE hμ hF i ht hf hfp
  have hic : (∫ t in Ico (0 : ℝ) 1,p t*f t)=∫ t in (0 : ℝ)..1,p t*f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Ico_eq_integral_Ioc]
  change (∫ t in Ico (0 : ℝ) 1,p t*f t)=_ at hflux
  rw [hic] at hflux
  have hsub : (∫ t in (0 : ℝ)..1,(q t-p t)*f t)=
      (∫ t in (0 : ℝ)..1,q t*f t)-(∫ t in (0 : ℝ)..1,p t*f t) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub ((hqc.mul hf.continuous).intervalIntegrable _ _)
      ((hcf.mul hf.continuous).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..1,(q t-p t)*f t)≤_
  rw [hsub]
  change (∫ t in (0 : ℝ)..1,q t*f t)=_ at hden
  rw [hden,hflux]
  have hcT : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
  have hi1 : Integrable (fun z : NormalBundle => axialNormalWeight i z*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    ((continuous_axialNormalWeight i).mul hcT).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun z : NormalBundle => f (z.1.1 i)*normalTest F hF.1.continuous z) (μ : Measure NormalBundle) :=
    (hcT.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hi1 hi2]
  calc
    (∫ z,axialNormalWeight i z*f (z.1.1 i)-f (z.1.1 i)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle))≤
        ∫ _ : NormalBundle,K^2*δ^2 ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae (hi1.sub hi2) (integrable_const _)
      filter_upwards [ha,hR] with z hzn hz
      have hcal := axialNormalCalibration_quadratic_lower N i z.1 (by rw [hzn]; exact z.2.property)
      rw [hzn] at hcal
      have hh := mul_le_mul_of_nonneg_right hcal (hf0 (z.1.1 i))
      change axialNormalWeight i z*f (z.1.1 i)-f (z.1.1 i)*normalTest F hF.1.continuous z≤K^2*δ^2
      by_cases hzero : f (z.1.1 i)=0
      · simp only [hzero,mul_zero,zero_mul,sub_self]
        positivity
      · have hn := hz.trans (mul_le_mul_of_nonneg_left (hδsupp _ hzero) hK)
        have hsq : ((z.2 : Cover) i)^2≤K^2*δ^2 := by
          have he := (sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (mul_nonneg hK hδ)).mpr hn
          simpa only [sq_abs,mul_pow] using he
        have hfa : ((z.2 : Cover) i)^2*f (z.1.1 i)≤((z.2 : Cover) i)^2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf1 (z.1.1 i)) (sq_nonneg ((z.2 : Cover) i))
        change (1-((z.2 : Cover) i)^2)*f (z.1.1 i)-f (z.1.1 i)*⟪(z.2 : Cover),F z.1⟫≤_
        dsimp only [F] at ⊢
        nlinarith
    _=K^2*(μ.mass : ℝ)*δ^2 := by
      simp only [integral_const,smul_eq_mul,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
      ring

theorem isMinimizerAt_axial_endpoint_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) (b : Bool) :
    axialSectionIntegral (openRepresentative E) i (divergence (axialNormalCalibration N i)) (if b then 1/2 else 0)=
      (μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hHo : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux (openRepresentative E) D.coordinate D.function := by
    intro D
    rw [directionalFlux_congr_ae hae,hH]
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  have hF := axialNormalCalibration_admissible hN hp i
  have hcf := continuous_axialSectionIntegral_of_boundary_null
    (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)
    (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  obtain ⟨K,hK⟩ := isMinimizerAt_normal_reflection_rate hV hE hm hμ hN hp ha hs
  apply axial_slice_endpoint_calibration (isOpen_openRepresentative E).measurableSet hvol hμo hHo hN hp ha i hc hcf
    (if b then 1/2 else 0) K.coe_nonneg
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo,ha] with z hz hzn
  have hh := hK i b z.1 z.1.property hz
  rw [hzn] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSlicePerimeter_le {E : Set Torus} {i : Fin 3} {t q : ℝ}
    (hb : ∀ (F : Cover → Cover),AdmissibleField F → (∀ x,F x i=0) →
      axialSectionIntegral E i (divergence F) t≤q) :
    axialSlicePerimeter E i t≤ENNReal.ofReal q := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro ht
  exact ENNReal.ofReal_le_ofReal (hb F hF ht)

lemma axialSlicePerimeter_ge {E : Set Torus} {i : Fin 3} {t : ℝ}
    {F : Cover → Cover} (hF : AdmissibleField F) (ht : ∀ x,F x i=0) :
    ENNReal.ofReal (axialSectionIntegral E i (divergence F) t)≤axialSlicePerimeter E i t := by
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le ht le_rfl))

theorem isMinimizerAt_axial_endpoint_perimeter_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) (b : Bool) :
    axialSlicePerimeter (openRepresentative E) i (if b then 1/2 else 0)=
      ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V)) := by
  apply le_antisymm
  · apply axialSlicePerimeter_le
    intro F hF ht
    exact isMinimizerAt_axial_slice_endpoint_bound hV hE hm hμ hN hp ha hs hsg hH hF i ht b
  · rw [← isMinimizerAt_axial_endpoint_calibration hV hE hm hμ hN hp ha hs hsg hH i b]
    exact axialSlicePerimeter_ge (axialNormalCalibration_admissible hN hp i) (axialNormalCalibration_axis N i)

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter_oai := @OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter_oai
