-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:55:14.6554+00:00
-- url     : https://prove2.me/submissions/134b994e-6c99-44be-a066-411d77a29423

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_linear_chart
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

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
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

lemma second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0≤deriv (deriv f) t := by
  by_contra hn
  have hn' : deriv (deriv f) t<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn' hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ ↦ f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
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

lemma cmcWeight_ge_one (p : Plane) : 1 ≤ cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
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

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

lemma cmcJacobian_symmetric (p v w : Plane) :
    ⟪v,cmcJacobian p w⟫=⟪cmcJacobian p v,w⟫ := by
  simp only [cmcJacobian_apply,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm v p]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
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

lemma continuous_local_scalar_product {f η : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hf : ContinuousOn f S) (hη : Continuous η)
    (hs : tsupport η⊆S) : Continuous (fun y ↦ f y*η y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact ((hf y (hs hy)).continuousAt (hS.mem_nhds (hs hy))).mul hη.continuousAt
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_local_integration_by_parts {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) (v : Plane) :
    (∫ y, fderiv ℝ g y v*ψ y)= -(∫ y,g y*fderiv ℝ ψ y v) := by
  have hdf : ContinuousOn (fun y ↦ fderiv ℝ g y v) S :=
    (hgc.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun y ↦ fderiv ℝ g y v*ψ y) :=
    (continuous_local_scalar_product hS hdf hψ.continuous hs).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun y ↦ g y*fderiv ℝ ψ y v) :=
    (hg.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ g y*ψ y) :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun y hy ↦ ((hgc y (hs hy)).contDiffAt (hS.mem_nhds (hs hy))).differentiableAt (by simp))
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
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

lemma cmcCompress_symm (p u v : Plane) : ⟪cmcCompress p u,v⟫=⟪u,cmcCompress p v⟫ := by
  simp only [cmcCompress_apply,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,conj_trivial,real_inner_comm u p]
  ring

lemma cmcCompress_sq (p v : Plane) :
    cmcCompress p (cmcCompress p v)=cmcWeight p • cmcJacobian p v := by
  rw [cmcCompress_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,cmcJacobian_apply,smul_sub,smul_smul,smul_smul]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  rw [mul_inv_cancel₀ hw,one_smul,sub_sub]
  rw [← add_smul]
  congr 1
  congr 1
  rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
  field_simp
  ring

lemma cmcStretch_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcStretch p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p+1 := by linarith
  have hi : (cmcWeight p+1)⁻¹≤1 := (inv_le_one₀ h0).mpr (by linarith)
  rw [cmcStretch_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p+1)⁻¹*⟪p,v⟫) • p‖ := norm_add_le _ _
    _ = ‖v‖+(cmcWeight p+1)⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

lemma cmcCompress_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcCompress p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p*(cmcWeight p+1) := by positivity
  have hi : (cmcWeight p*(cmcWeight p+1))⁻¹≤1 := (inv_le_one₀ h0).mpr (by nlinarith)
  rw [cmcCompress_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = ‖v‖+(cmcWeight p*(cmcWeight p+1))⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_HolderNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose (v : Plane) : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+
    v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
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

lemma planeDivergence_continuous {F : Plane → Plane} (hF : ContDiff ℝ 1 F) :
    Continuous (planeDivergence F) := by
  have hd := hF.continuous_fderiv (by simp)
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const))

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

lemma plane_divergence_integration_by_parts {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ y,planeDivergence F y*ψ y)= -(∫ y,fderiv ℝ ψ y (F y)) := by
  have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hi (i : Fin 2) : Integrable (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single i 1)) i*ψ y) :=
    (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous.comp
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hj (i : Fin 2) : Integrable (fun y ↦ F y i*fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    ((hcomp i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ _).mul_left
  have hpart (i : Fin 2) := C1_local_integration_by_parts isOpen_univ (hcomp i).continuous
    (hcomp i).contDiffOn hψ hc (subset_univ _) (EuclideanSpace.single i 1)
  simp_rw [plane_component_fderiv hF] at hpart
  have he (y : Plane) : fderiv ℝ ψ y (F y)=
      F y 0*fderiv ℝ ψ y (EuclideanSpace.single 0 1)+
      F y 1*fderiv ℝ ψ y (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose (F y)]
    simp
  simp_rw [planeDivergence,add_mul,he]
  rw [integral_add (hi 0) (hi 1),hpart 0,hpart 1,integral_add (hj 0) (hj 1)]
  ring

lemma classical_divergence_of_weak {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {S : Set Plane} (hS : IsOpen S) {H : ℝ}
    (hw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆S →
      (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y)) :
    ∀ y∈S,planeDivergence F y= -H := by
  have hd := (planeDivergence_continuous hF).add (continuous_const (y := H))
  have hae := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrable.locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · have hae' : (fun y ↦ planeDivergence F y+H)=ᵐ[volume.restrict S] (fun _ ↦ (0:ℝ)) := by
      change ∀ᵐ y ∂volume.restrict S,planeDivergence F y+H=0
      rw [ae_restrict_iff' hS.measurableSet]
      exact hae
    have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hd.continuousOn continuousOn_const
    intro y hy
    exact eq_neg_of_add_eq_zero_left (he hy)
  · have hi : Integrable (fun y ↦ planeDivergence F y*ψ y) volume := ((planeDivergence_continuous hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable (fun y ↦ H*ψ y) volume := (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul H
    simp only [smul_eq_mul,Pi.add_apply,mul_add]
    simp_rw [mul_comm (ψ _) (planeDivergence F _),mul_comm (ψ _) H]
    rw [integral_add hi hj,plane_divergence_integration_by_parts hF (hψ.of_le (by simp)) hc,
      hw ψ hψ hc hs,integral_const_mul]
    ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
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

lemma plane_gradient_mul {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ f y*g y) x=f x • gradient g x+g x • gradient f x := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right,inner_add_right,real_inner_smul_right,
    fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,starRingEnd_apply,star_trivial]

lemma plane_gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_components (u v : Plane) : ⟪u,v⟫=u 0*v 0+u 1*v 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,star_trivial]
  ring

lemma plane_gradient_component (f : Plane → ℝ) (y : Plane) (i : Fin 2) :
    gradient f y i=fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma planeDivergence_add {F G : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    planeDivergence (fun z ↦ F z+G z) y=planeDivergence F y+planeDivergence G y := by
  simp only [planeDivergence,fderiv_fun_add hF hG,add_apply,PiLp.add_apply]
  ring

lemma planeDivergence_smul {a : Plane → ℝ} {F : Plane → Plane} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hF : DifferentiableAt ℝ F y) :
    planeDivergence (fun z ↦ a z • F z) y=
      a y*planeDivergence F y+⟪gradient a y,F y⟫ := by
  rw [plane_inner_components]
  simp only [plane_gradient_component,planeDivergence,fderiv_fun_smul ha hF,
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_hessian_direction {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v : Plane) : fderiv ℝ (gradient g) y v=
      gradient (fun z ↦ fderiv ℝ g z v) y := by
  ext i
  rw [← plane_component_fderiv ((plane_gradient_contDiff hg).of_le (by simp))]
  simp_rw [plane_gradient_component]
  rw [fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v _

lemma plane_hessian_symmetric {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v w : Plane) : ⟪fderiv ℝ (gradient g) y v,w⟫=⟪v,fderiv ℝ (gradient g) y w⟫ := by
  rw [plane_hessian_direction hg,plane_hessian_direction hg]
  conv_rhs => rw [real_inner_comm]
  rw [inner_gradient_left,inner_gradient_left,fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
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

lemma planeTrace_comp_comm (A B : Plane →L[ℝ] Plane) :
    planeTrace (A.comp B)=planeTrace (B.comp A) := by
  simp only [planeTrace,Fin.sum_univ_two,ContinuousLinearMap.comp_apply]
  rw [plane_decompose (B (EuclideanSpace.single 0 1)),
    plane_decompose (B (EuclideanSpace.single 1 1)),
    plane_decompose (A (EuclideanSpace.single 0 1)),
    plane_decompose (A (EuclideanSpace.single 1 1))]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

lemma LinearCMCEquation.classical_zero {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hU : IsOpen U)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U) :
    ∀ y∈U,planeDivergence (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) y=0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) :=
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).clm_apply (plane_gradient_contDiff hf)
  have ht := classical_divergence_of_weak (H := 0) (hF.of_le (by simp)) hU
    (fun ψ hψ hc hs ↦ by simpa only [sub_zero,zero_mul] using hw ψ hψ hc hs)
  simpa only [neg_zero] using ht

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
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

lemma directionalNormalScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v x : Cover) :
    (directionalNormalScalar N hN hp v).val x=⟪v,N x⟫ := by
  simp only [directionalNormalScalar,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,normalComponentScalar_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

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

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Translation
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

lemma smooth_line_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) (t : ℝ) :
    deriv (fun s : ℝ => f (x+s • v)) t= fderiv ℝ f (x+t • v) v := by
  simpa only [Function.comp_def,id_eq,one_smul] using ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const v |>.const_add x)).deriv

lemma smooth_line_second_deriv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x v : Plane) :
    deriv (deriv (fun s : ℝ => f (x+s • v))) 0=
      ⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have he : deriv (fun s : ℝ => f (x+s • v))=
      (fun t => fderiv ℝ f (x+t • v) v) := funext (smooth_line_deriv hf x v)
  rw [he]
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) :=
    hf.fderiv_right (by simp) |>.clm_apply contDiff_const
  rw [smooth_line_deriv hg x v 0]
  simp only [zero_smul,add_zero]
  rw [plane_hessian_direction hf,inner_gradient_left]

lemma plane_hessian_nonneg_of_local_min {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane} (hm : IsLocalMin f x) (v : Plane) :
    0≤⟪fderiv ℝ (gradient f) x v,v⟫ := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (show Continuous (fun t : ℝ => x+t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
  have hm' : IsLocalMin (fun t : ℝ => f (x+t • v)) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), f (x+0 • v)≤f (x+t • v)
    simpa only [zero_smul,add_zero] using ht.eventually hm
  rw [← smooth_line_second_deriv hf x v]
  exact second_derivative_nonneg_of_local_min hm'
    (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt

lemma planeFrameOperator_nonneg_of_local_min (B : Plane → Fin 2 → Plane)
    (b : Plane → Plane) {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} (hm : IsLocalMin f x) : 0≤planeFrameOperator B b f x := by
  have hz : gradient f x=0 := by simp [gradient,hm.fderiv_eq_zero]
  simp only [planeFrameOperator,hz,inner_zero_left,add_zero]
  exact Finset.sum_nonneg (fun i _ => plane_hessian_nonneg_of_local_min hf hm (B x i))

lemma planeFrameOperator_sub (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f g : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Plane) : planeFrameOperator B b (fun y => f y-g y) x=
      planeFrameOperator B b f x-planeFrameOperator B b g x := by
  have he : gradient (fun y => f y-g y)=fun y => gradient f y-gradient g y := by
    funext y
    simp only [gradient,fderiv_fun_sub (hf.differentiable (by simp) y)
      (hg.differentiable (by simp) y),map_sub]
  rw [planeFrameOperator,he,fderiv_fun_sub
    ((plane_gradient_contDiff hf).differentiable (by simp) x)
    ((plane_gradient_contDiff hg).differentiable (by simp) x)]
  simp only [sub_apply,inner_sub_left,Finset.sum_sub_distrib,planeFrameOperator]
  ring

lemma planeFrameOperator_smul (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x : Plane) :
    planeFrameOperator B b (fun y => c*f y) x=c*planeFrameOperator B b f x := by
  have he : gradient (fun y => c*f y)=fun y => c • gradient f y := by
    funext y
    simp only [gradient,show (fun y => c*f y)=(fun y => c • f y) from rfl,
      fderiv_fun_const_smul (hf.differentiable (by simp) y),map_smul]
  rw [planeFrameOperator,he,fderiv_fun_const_smul
    ((plane_gradient_contDiff hf).differentiable (by simp) x)]
  simp only [smul_apply,real_inner_smul_left,← Finset.mul_sum,planeFrameOperator]
  ring

theorem planeFrameOperator_annulus_comparison (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : Plane) {r R : ℝ} (hr : 0 < r) (hrR : r<R)
    (hbd : ∀ x,‖x-c‖=r ∨ ‖x-c‖=R → 0≤f x)
    (hL : ∀ x,r<‖x-c‖ → ‖x-c‖<R → planeFrameOperator B b f x<0) :
    ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤f x := by
  let K : Set Plane := Metric.closedBall c R \ Metric.ball c r
  have hK : IsCompact K := (isCompact_closedBall c R).diff Metric.isOpen_ball
  have hKne : K.Nonempty := by
    obtain ⟨point,hpoint⟩ := (NormedSpace.sphere_nonempty (x := c)).2 hr.le
    have hdist : dist point c=r := hpoint
    refine ⟨point,?_⟩
    change dist point c≤R ∧ ¬ dist point c < r
    rw [hdist]
    exact ⟨hrR.le,lt_irrefl r⟩
  intro x hrx hxR
  have hxK : x∈K := by simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,
    not_lt] using And.intro hxR hrx
  obtain ⟨y,hyK,hym⟩ := hK.exists_isMinOn hKne hf.continuous.continuousOn
  have hyr : r≤‖y-c‖ := by simpa only [K,Set.mem_sdiff,Metric.mem_ball,dist_eq_norm,not_lt] using hyK.2
  have hyR : ‖y-c‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hyK.1
  have hy0 : 0≤f y := by
    by_cases h1 : ‖y-c‖=r
    · exact hbd y (Or.inl h1)
    by_cases h2 : ‖y-c‖=R
    · exact hbd y (Or.inr h2)
    have hri : r<‖y-c‖ := lt_of_le_of_ne hyr (Ne.symm h1)
    have hRi : ‖y-c‖<R := lt_of_le_of_ne hyR h2
    have hn : K∈𝓝 y := by
      have ho : IsOpen {z : Plane | r<‖z-c‖ ∧ ‖z-c‖<R} :=
        (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
      apply mem_of_superset (ho.mem_nhds ⟨hri,hRi⟩)
      intro z hz
      simpa only [K,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_eq_norm,not_lt] using
        And.intro hz.2.le hz.1.le
    have hm : IsLocalMin f y := hym.isLocalMin hn
    exact False.elim ((not_lt_of_ge (planeFrameOperator_nonneg_of_local_min B b hf hm))
      (hL y hri hRi))
  exact hy0.trans (hym hxK)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_sub {F G : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Plane) :
    planeDivergence (fun y => F y-G y) x=planeDivergence F x-planeDivergence G x := by
  simp only [planeDivergence,fderiv_fun_sub (hF.differentiable (by simp) x)
    (hG.differentiable (by simp) x),sub_apply,PiLp.sub_apply]
  ring

lemma planeDivergence_contDiff {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : PlaneSmooth (planeDivergence F) := by
  unfold planeDivergence
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const))

lemma planeElliptic_contDiff {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) : PlaneSmooth (planeElliptic A f) :=
  planeDivergence_contDiff (hA.clm_apply (plane_gradient_contDiff hf))

lemma planeDrift_contDiff {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : PlaneSmooth f) : PlaneSmooth (planeDrift b f) :=
  (hf.fderiv_right (by simp)).clm_apply hb

lemma planeDrift_compact {b : Plane → Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeDrift b f) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDrift,hz])

lemma planeDivergence_compact {F : Plane → Plane} (hc : HasCompactSupport F) :
    HasCompactSupport (planeDivergence F) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  exact hx (by simp [planeDivergence,hz])

lemma planeElliptic_compact {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeElliptic A f) := by
  apply planeDivergence_compact
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [hz])

lemma planeDivergence_integral_zero {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    (∫ x,planeDivergence F x)=0 := by
  have hcomp (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hcc (i : Fin 2) : HasCompactSupport (fun y => F y i) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hi (i : Fin 2) : Integrable (fun y => fderiv ℝ (fun z => F z i) y
      (EuclideanSpace.single i 1)) :=
    (((hcomp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcc i).fderiv_apply ℝ _)
  have hp (i : Fin 2) := C1_local_integration_by_parts (g := fun _ : Plane => (1:ℝ)) isOpen_univ continuous_const
    contDiffOn_const ((hcomp i).of_le (by simp)) (hcc i)
    (subset_univ _) (EuclideanSpace.single i 1)
  simp only [fderiv_fun_const,one_mul] at hp
  simp only [plane_component_fderiv (hF.of_le (by simp))] at hi hp
  have hz (i : Fin 2) : (∫ y, ((fderiv ℝ F y) (EuclideanSpace.single i 1)) i)=0 := by
    simpa using (hp i).symm
  simp only [planeDivergence]
  rw [integral_add (hi 0) (hi 1),hz 0,hz 1,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeEnergy_contDiff {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) : PlaneSmooth (planeEnergy A u) :=
  (plane_gradient_contDiff hu).inner ℝ (hA.clm_apply (plane_gradient_contDiff hu))

lemma planeEnergy_compact {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hc : HasCompactSupport u) : HasCompactSupport (planeEnergy A u) := by
  apply (plane_gradient_compact hc).mono
  intro x hx hz
  exact hx (by simp [planeEnergy,hz])

lemma planeEnergy_fderiv {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x v : Plane) :
    fderiv ℝ (planeEnergy A u) x v=
      2*⟪fderiv ℝ (gradient u) x v,A x (gradient u x)⟫+
      ⟪gradient u x,(fderiv ℝ A x v) (gradient u x)⟫ := by
  have hg := (plane_gradient_contDiff hu).differentiable (by simp) x
  have ha := hA.differentiable (by simp) x
  unfold planeEnergy
  rw [fderiv_inner_apply ℝ hg (ha.clm_apply hg),fderiv_clm_apply ha hg]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,inner_add_right]
  rw [hAs x (gradient u x) (fderiv ℝ (gradient u) x v)]
  ring

lemma planeDrift_fderiv {b : Plane → Plane} {u : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) (x v : Plane) :
    fderiv ℝ (planeDrift b u) x v=
      ⟪fderiv ℝ (gradient u) x (b x),v⟫+⟪gradient u x,fderiv ℝ b x v⟫ := by
  have he : planeDrift b u=fun y => ⟪gradient u y,b y⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [he,fderiv_inner_apply ℝ ((plane_gradient_contDiff hu).differentiable (by simp) x)
    (hb.differentiable (by simp) x),plane_hessian_symmetric hu]
  rw [real_inner_comm v]
  ring

lemma planeRellichFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u) :
    ContDiff ℝ (⊤ : ℕ∞) (planeRellichFlux A b u) :=
  ((((contDiff_const.mul (planeDrift_contDiff hb hu)).add
    ((planeDivergence_contDiff hb).mul hu)).smul
      (hA.clm_apply (plane_gradient_contDiff hu))).sub
    ((planeEnergy_contDiff hA hu).smul hb)).sub
    ((contDiff_const.mul (hu.pow 2)).smul
      (hA.clm_apply (plane_gradient_contDiff (planeDivergence_contDiff hb))))

lemma planeRellichFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (planeRellichFlux A b u) := by
  apply (((planeDrift_compact (b := b) hc).mul_left.add hc.mul_left).smul_right.sub
    (planeEnergy_compact hc).smul_right).sub
  have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  exact hpow.mul_left.smul_right

theorem planeRellichFlux_divergence {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeDivergence (planeRellichFlux A b u) x=
      planeElliptic A u x*(2*planeDrift b u x+planeDivergence b x*u x)+
      2*⟪gradient u x,fderiv ℝ b x (A x (gradient u x))⟫-
      ⟪gradient u x,(fderiv ℝ A x (b x)) (gradient u x)⟫-
      (1/2:ℝ)*planeElliptic A (planeDivergence b) x*u x^2 := by
  have hd := planeDivergence_contDiff hb
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hD := hA.clm_apply (plane_gradient_contDiff hd)
  have hK : PlaneSmooth (fun y => 2*planeDrift b u y+planeDivergence b y*u y) :=
    (contDiff_const.mul (planeDrift_contDiff hb hu)).add (hd.mul hu)
  have hE := planeEnergy_contDiff hA hu
  have hW : PlaneSmooth (fun y => (1/2:ℝ)*u y^2) := contDiff_const.mul (hu.pow 2)
  unfold planeRellichFlux
  erw [planeDivergence_sub ((hK.smul hG).sub (hE.smul hb)) (hW.smul hD),
    planeDivergence_sub (hK.smul hG) (hE.smul hb),
    planeDivergence_smul (hK.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hE.differentiable (by simp) x) (hb.differentiable (by simp) x),
    planeDivergence_smul (hW.differentiable (by simp) x) (hD.differentiable (by simp) x)]
  simp only [inner_gradient_left]
  rw [fderiv_fun_add ((contDiff_const.mul (planeDrift_contDiff hb hu)).differentiable (by simp) x)
      ((hd.mul hu).differentiable (by simp) x),
    fderiv_const_mul ((planeDrift_contDiff hb hu).differentiable (by simp) x),
    fderiv_fun_mul (hd.differentiable (by simp) x) (hu.differentiable (by simp) x),
    fderiv_const_mul ((hu.pow 2).differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [planeDrift_fderiv hb hu,planeEnergy_fderiv hA hu hAs]
  simp only [← inner_gradient_left,planeElliptic,planeEnergy]
  rw [hAs x (gradient u x) (gradient (planeDivergence b) x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeCarlemanFlux_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeCarlemanFlux A b q τ u) :=
  by
  unfold planeCarlemanFlux
  exact ((planeRellichFlux_contDiff hA hb hu).const_smul (2*τ)).add
    ((((contDiff_const (c := 2*τ^3)).mul hq).mul (hu.pow 2)).smul hb)

lemma planeCarlemanFlux_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanFlux A b q τ u) := by
  unfold planeCarlemanFlux
  apply HasCompactSupport.add
  · apply (planeRellichFlux_compact (A := A) (b := b) hc).mono
    intro x hx hz
    exact hx (by simp only [hz,smul_zero])
  · have hpow : HasCompactSupport (fun x => u x^2) := hc.mono (by
      intro x hx hz
      exact hx (by simp [hz]))
    exact hpow.mul_left.smul_right

lemma planeCarlemanP_contDiff {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u) (τ : ℝ) :
    PlaneSmooth (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_contDiff hA hu).add ((contDiff_const.mul hq).mul hu)).add
    (contDiff_const.mul ((contDiff_const.mul (planeDrift_contDiff hb hu)).add
      ((planeDivergence_contDiff hb).mul hu)))

lemma planeCarlemanP_compact {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hc : HasCompactSupport u) (τ : ℝ) :
    HasCompactSupport (planeCarlemanP A b q τ u) :=
  by
  unfold planeCarlemanP planeCarlemanS planeCarlemanT
  exact ((planeElliptic_compact hc).add hc.mul_left).add
    (((planeDrift_compact hc).mul_left.add hc.mul_left).mul_left)

theorem planeCarleman_pointwise {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) (x : Plane) :
    (planeCarlemanP A b q τ u x)^2+planeDivergence (planeCarlemanFlux A b q τ u) x=
      (planeCarlemanS A q τ u x)^2+(planeCarlemanT b τ u x)^2+
      τ*planeCarlemanR A b x (gradient u x)+
      (2*τ^3*planeDrift b q x-τ*planeElliptic A (planeDivergence b) x)*u x^2 := by
  have hf := planeRellichFlux_contDiff hA hb hu
  have hk : PlaneSmooth (fun y => 2*τ^3*q y*u y^2) :=
    (contDiff_const.mul hq).mul (hu.pow 2)
  unfold planeCarlemanFlux
  erw [planeDivergence_add ((hf.const_smul (2*τ)).differentiable (by simp) x)
      ((hk.smul hb).differentiable (by simp) x),
    planeDivergence_smul (differentiableAt_const (2*τ)) (hf.differentiable (by simp) x),
    planeDivergence_smul (hk.differentiable (by simp) x) (hb.differentiable (by simp) x)]
  simp only [add_zero,inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply]
  rw [planeRellichFlux_divergence hA hb hu hAs,
    fderiv_fun_mul ((contDiff_const.mul hq).differentiable (by simp) x)
      ((hu.pow 2).differentiable (by simp) x),
    fderiv_const_mul (hq.differentiable (by simp) x),
    fderiv_fun_pow 2 (hu.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  simp only [planeCarlemanP,planeCarlemanS,planeCarlemanT,planeCarlemanR,planeDrift]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma carleman_scalar_coercivity {C D Q c τ E R S T z q d l : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ)
    (hpseudo : 2≤2*c-(C+1)*Q) (hR : -C*E≤R) (hq : q≤Q)
    (hd : c≤d) (hl : l≤D) :
    τ*E+τ^3*z^2≤S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E) := by
  have ht : 0≤τ := by linarith
  have ha : 0≤C+1 := by linarith
  have ht2 : τ≤τ^2 := by nlinarith
  have hb : 0≤τ^3-D*τ-(C+1)^2*τ^2 := by
    have h₁ := mul_le_mul_of_nonneg_left ht2 hD
    have h₂ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg τ)
    nlinarith
  have hs : 0≤S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2 := by
    nlinarith only [sq_nonneg (S+(C+1)*τ*z),sq_nonneg S,
      sq_nonneg ((C+1)*τ*z)]
  have h₁ : 0≤τ*(R+C*E) := mul_nonneg ht (by linarith)
  have h₂ : 0≤(2*τ^3*(d-c))*z^2 :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hd)) (sq_nonneg z)
  have h₃ : 0≤((C+1)*τ^3*(Q-q))*z^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg ht _)) (sub_nonneg.mpr hq)) (sq_nonneg z)
  have h₄ : 0≤(τ*(D-l))*z^2 :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hl)) (sq_nonneg z)
  have h₅ : 0≤(τ^3*(2*c-(C+1)*Q-2))*z^2 :=
    mul_nonneg (mul_nonneg (pow_nonneg ht _) (by linarith)) (sq_nonneg z)
  have h₆ := mul_nonneg hb (sq_nonneg z)
  have he : S^2+T^2+τ*R+(2*τ^3*d-τ*l)*z^2+
      (C+1)*τ*(z*(S-τ^2*q*z)+E)-(τ*E+τ^3*z^2)=
      T^2+(S^2+(C+1)*τ*S*z+(C+1)^2*τ^2*z^2)+τ*(R+C*E)+
      (2*τ^3*(d-c))*z^2+((C+1)*τ^3*(Q-q))*z^2+
      (τ*(D-l))*z^2+(τ^3*(2*c-(C+1)*Q-2))*z^2+
      (τ^3-D*τ-(C+1)^2*τ^2)*z^2 := by ring
  have hh := add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (sq_nonneg T) hs) h₁) h₂) h₃) h₄) h₅) h₆
  rw [← he] at hh
  exact sub_nonneg.mp hh

lemma plane_energy_flux_divergence {A : Plane → Plane →L[ℝ] Plane} {u : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hu : PlaneSmooth u) (x : Plane) :
    planeDivergence (fun y => u y • A y (gradient u y)) x=
      u x*planeElliptic A u x+planeEnergy A u x := by
  exact planeDivergence_smul (hu.differentiable (by simp) x)
    ((hA.clm_apply (plane_gradient_contDiff hu)).differentiable (by simp) x)

theorem planeCarleman_coercive {A : Plane → Plane →L[ℝ] Plane} {b : Plane → Plane}
    {q u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hq : PlaneSmooth q) (hu : PlaneSmooth u)
    (hc : HasCompactSupport u) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport u⊆U)
    (hdata : PlaneCarlemanData A b q U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    (∫ x,τ*planeEnergy A u x+τ^3*u x^2)≤
      ∫ x,(planeCarlemanP A b q τ u x)^2 := by
  let F : Plane → Plane := fun x => planeCarlemanFlux A b q τ u x+
    ((C+1)*τ) • (u x • A x (gradient u x))
  have hG := hA.clm_apply (plane_gradient_contDiff hu)
  have hf : ContDiff ℝ (⊤ : ℕ∞) F :=
    (planeCarlemanFlux_contDiff hA hb hq hu τ).add ((hu.smul hG).const_smul ((C+1)*τ))
  have hgc : HasCompactSupport (fun x => ((C+1)*τ) • (u x • A x (gradient u x))) := by
    apply hc.mono
    intro x hx hz
    exact hx (by simp [hz])
  have hfc : HasCompactSupport F :=
    (planeCarlemanFlux_compact (A := A) (b := b) (q := q) hc τ).add hgc
  have hdiv (x : Plane) : planeDivergence F x=
      planeDivergence (planeCarlemanFlux A b q τ u) x+
        (C+1)*τ*(u x*planeElliptic A u x+planeEnergy A u x) := by
    dsimp only [F]
    erw [planeDivergence_add ((planeCarlemanFlux_contDiff hA hb hq hu τ).differentiable (by simp) x)
        (((hu.smul hG).const_smul ((C+1)*τ)).differentiable (by simp) x),
      planeDivergence_smul (differentiableAt_const ((C+1)*τ)) ((hu.smul hG).differentiable (by simp) x)]
    simp only [inner_gradient_left,fderiv_fun_const,Pi.zero_apply,zero_apply,add_zero]
    erw [plane_energy_flux_divergence hA hu]
  have hpoint (x : Plane) : τ*planeEnergy A u x+τ^3*u x^2≤
      (planeCarlemanP A b q τ u x)^2+planeDivergence F x := by
    rw [hdiv,← add_assoc,planeCarleman_pointwise hA hb hq hu hAs τ]
    by_cases hx : x∈tsupport u
    · have hh := carleman_scalar_coercivity hdata.C_nonneg hdata.D_nonneg hτ hbudget
        hdata.pseudoconvex (hdata.principal x (hs hx) (gradient u x))
        (hdata.weight_bound x (hs hx)) (hdata.transport_bound x (hs hx))
        (hdata.remainder_bound x (hs hx))
        (S := planeCarlemanS A q τ u x) (T := planeCarlemanT b τ u x) (z := u x)
      simpa only [planeEnergy,planeCarlemanS,add_sub_cancel_right] using hh
    · have hz : u x=0 := image_eq_zero_of_notMem_tsupport hx
      have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp only [planeEnergy,hg,inner_zero_left,mul_zero,hz,zero_pow (by decide : (2:ℕ)≠0),
        planeCarlemanR,map_zero,sub_self,add_zero,zero_mul]
      positivity
  have huc : HasCompactSupport (fun x => u x^2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  have hi : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact hc)).const_mul τ).add
      (((hu.continuous.pow 2).integrable_of_hasCompactSupport huc).const_mul (τ^3))
  have hp := planeCarlemanP_contDiff hA hb hq hu τ
  have hpc := planeCarlemanP_compact (A := A) (b := b) (q := q) hc τ
  have hj : Integrable (fun x => (planeCarlemanP A b q τ u x)^2) :=
    (hp.continuous.pow 2).integrable_of_hasCompactSupport (hpc.mono (by
      intro x hx hz
      exact hx (by simp [hz])))
  have hk : Integrable (planeDivergence F) :=
    (planeDivergence_contDiff hf).continuous.integrable_of_hasCompactSupport
    (planeDivergence_compact hfc)
  have hm := integral_mono hi (hj.add hk) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add hj hk,planeDivergence_integral_zero hf hfc,add_zero] at hm
  exact hm

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneQuadraticWeight
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

lemma planeQuadraticWeight_smooth (a n : Plane) (κ ε : ℝ) :
    PlaneSmooth (planeQuadraticWeight a n κ ε) :=
  ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).pow 2))).sub
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma planeQuadraticWeight_fderiv (a n : Plane) (κ ε : ℝ) (x : Plane) :
    fderiv ℝ (planeQuadraticWeight a n κ ε) x=
      innerSL ℝ n+(κ*⟪n,x-a⟫) • innerSL ℝ n-ε • innerSL ℝ (x-a) := by
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (hl.add ((hl.pow 2).const_mul (κ/2))).sub
    (((hasFDerivAt_id x).sub_const a).norm_sq.const_mul (ε/2))
  change HasFDerivAt (planeQuadraticWeight a n κ ε) _ x at hd
  rw [hd.fderiv]
  ext v
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul,
    nsmul_eq_mul,Nat.cast_ofNat,Function.comp_apply,id_eq]
  ring

lemma planeQuadraticWeight_gradient (a n : Plane) (κ ε : ℝ) (x : Plane) :
    gradient (planeQuadraticWeight a n κ ε) x=
      n+(κ*⟪n,x-a⟫) • n-ε • (x-a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,planeQuadraticWeight_fderiv]
  simp only [add_apply,sub_apply,smul_apply,innerSL_apply_apply,
    inner_sub_left,inner_add_left,real_inner_smul_left,smul_eq_mul]

lemma planeQuadraticWeight_hessian (a n : Plane) (κ ε : ℝ) (x v : Plane) :
    fderiv ℝ (gradient (planeQuadraticWeight a n κ ε)) x v=
      (κ*⟪n,v⟫) • n-ε • v := by
  have he : gradient (planeQuadraticWeight a n κ ε)=
      fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a) :=
    funext (planeQuadraticWeight_gradient a n κ ε)
  rw [he]
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (((hl.const_mul κ).smul_const n).const_add n).sub
    (((hasFDerivAt_id x).sub_const a).const_smul ε)
  change HasFDerivAt (fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a)) _ x at hd
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]

lemma planeQuadraticWeight_gradient_center (a n : Plane) (κ ε : ℝ) :
    gradient (planeQuadraticWeight a n κ ε) a=n := by
  simp [planeQuadraticWeight_gradient]

lemma quadratic_weight_R {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) (x w : Plane) :
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w=
      4*κ*⟪n,A x w⟫^2-4*ε*‖A x w‖^2+
      4*⟪w,(fderiv ℝ A x (A x w)) (gradient (planeQuadraticWeight a n κ ε) x)⟫-
      2*⟪w,(fderiv ℝ A x (A x (gradient (planeQuadraticWeight a n κ ε) x))) w⟫ := by
  have hg := plane_gradient_contDiff (planeQuadraticWeight_smooth a n κ ε)
  rw [planeCarlemanR,fderiv_clm_apply (hA.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    planeQuadraticWeight_hessian,map_sub,map_smul,inner_add_right,inner_sub_right,real_inner_smul_right]
  rw [hAs x w n,hAs x w (A x w),real_inner_self_eq_norm_sq]
  ring

lemma quadratic_weight_transport_center {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) :
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a=
      2*κ*⟪n,A a n⟫^2-2*ε*‖A a n‖^2+⟪n,(fderiv ℝ A a (A a n)) n⟫ := by
  rw [planeDrift,planeEnergy_fderiv hA (planeQuadraticWeight_smooth a n κ ε) hAs,
    planeQuadraticWeight_gradient_center,planeQuadraticWeight_hessian]
  simp only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_clm_bound (A : Plane →L[ℝ] Plane) (v w : Plane) :
    |⟪v,A w⟫|≤‖v‖*‖A‖*‖w‖ := by
  calc
    |⟪v,A w⟫|≤‖v‖*‖A w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖A‖*‖w‖) := mul_le_mul_of_nonneg_left (A.le_opNorm w) (norm_nonneg _)
    _ = _ := by ring

lemma plane_inner_double_clm_bound (B : Plane →L[ℝ] (Plane →L[ℝ] Plane)) (v w z : Plane) :
    |⟪v,B w z⟫|≤‖v‖*‖B‖*‖w‖*‖z‖ := by
  calc
    |⟪v,B w z⟫|≤‖v‖*‖B w‖*‖z‖ := plane_inner_clm_bound _ _ _
    _ ≤ ‖v‖*(‖B‖*‖w‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (B.le_opNorm w) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_weight_R_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) {κ ε M K P : ℝ} (hκ : 0≤κ) (hε : 0≤ε)
    {x : Plane} (hM : ‖A x‖≤M) (hK : ‖fderiv ℝ A x‖≤K)
    (hP : ‖gradient (planeQuadraticWeight a n κ ε) x‖≤P) (w : Plane) :
    -(4*ε*M^2+6*K*M*P)*‖w‖^2≤
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w := by
  let p := gradient (planeQuadraticWeight a n κ ε) x
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A x)).trans hK
  have hP0 : 0≤P := (norm_nonneg _).trans hP
  have haw : ‖A x w‖≤M*‖w‖ := (A x).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hap : ‖A x p‖≤M*P := ((A x).le_opNorm p).trans
    (mul_le_mul hM hP (norm_nonneg _) hM0)
  have h₁ : |⟪w,(fderiv ℝ A x (A x w)) p⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x w‖*‖p‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*‖w‖)*P := by gcongr
      _ = _ := by ring
  have h₂ : |⟪w,(fderiv ℝ A x (A x p)) w⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x p‖*‖w‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*P)*‖w‖ := by gcongr
      _ = _ := by ring
  have hs : ‖A x w‖^2≤M^2*‖w‖^2 := by
    calc
      _ ≤ (M*‖w‖)^2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)) |>.mpr haw
      _ = _ := by ring
  have hsq : 0≤4*κ*⟪n,A x w⟫^2 := by positivity
  have hneg := mul_le_mul_of_nonneg_left hs (show 0≤4*ε by positivity)
  rw [quadratic_weight_R hA hAs]
  have hleft := (abs_le.mp h₁).1
  have hright := (abs_le.mp h₂).2
  dsimp only [p] at hleft hright
  nlinarith only [hleft,hright,hneg,hsq]

lemma quadratic_weight_transport_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {κ ε M K ℓ : ℝ}
    (hκ : 0≤κ) (hε : 0≤ε) (hℓ : 0≤ℓ)
    (hell : ℓ≤⟪n,A a n⟫) (hM : ‖A a‖≤M) (hK : ‖fderiv ℝ A a‖≤K) :
    2*κ*ℓ^2-2*ε*M^2-K*M≤
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a := by
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A a)).trans hK
  have han : ‖A a n‖≤M := by
    simpa only [hn,mul_one] using ((A a).le_opNorm n).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg n))
  have he : |⟪n,(fderiv ℝ A a (A a n)) n⟫|≤K*M := by
    calc
      _ ≤ ‖n‖*‖fderiv ℝ A a‖*‖A a n‖*‖n‖ := plane_inner_double_clm_bound _ _ _ _
      _ = ‖fderiv ℝ A a‖*‖A a n‖ := by rw [hn]; ring
      _ ≤ K*M := mul_le_mul hK han (norm_nonneg _) hK0
  have hs₁ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ hℓ (hℓ.trans hell) |>.mpr hell) (show 0≤2*κ by positivity)
  have hs₂ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (norm_nonneg _) hM0 |>.mpr han) (show 0≤2*ε by positivity)
  rw [quadratic_weight_transport_center hA hAs]
  linarith [(abs_le.mp he).1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ellipticity_perturb {A B : Plane →L[ℝ] Plane} {ℓ δ : ℝ}
    (hA : ∀ v,ℓ*‖v‖^2≤⟪v,A v⟫) (hAB : ‖B-A‖≤δ) (v : Plane) :
    (ℓ-δ)*‖v‖^2≤⟪v,B v⟫ := by
  have hh := plane_inner_clm_bound (B-A) v v
  have hd : |⟪v,(B-A) v⟫|≤δ*‖v‖^2 := by
    calc
      _ ≤ ‖v‖*‖B-A‖*‖v‖ := hh
      _ ≤ ‖v‖*δ*‖v‖ := by gcongr
      _ = _ := by ring
  simp only [sub_apply,inner_sub_right] at hd
  linarith [(abs_le.mp hd).1,hA v]

theorem planeCarleman_weight_exists {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {ℓ ε : ℝ} (hℓ : 0<ℓ) (hε : 0<ε)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫) :
    ∃ κ>0,∃ r>0,∃ C D Q c : ℝ,
      PlaneCarlemanData A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
        (planeEnergy A (planeQuadraticWeight a n κ ε)) (Metric.ball a r) C D Q c ∧
      ∀ x∈Metric.ball a r,∀ v,(ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
  let M := ‖A a‖+1
  let K := ‖fderiv ℝ A a‖+1
  let B := 4*ε*M^2+12*K*M
  let C := B/(ℓ/2)
  let Q := 4*M
  let c := ((C+1)*Q+2)/2
  have hM : 0<M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := div_nonneg hB (by positivity)
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let κ := max 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2))
  have hκ : 0<κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlarge : c+2*ε*M^2+K*M+1≤2*κ*ℓ^2 := by
    have hh := (div_le_iff₀ (show 0<2*ℓ^2 by positivity)).mp
      (le_max_right 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2)))
    dsimp only [κ]
    nlinarith only [hh]
  let φ := planeQuadraticWeight a n κ ε
  let b : Plane → Plane := fun y => A y (gradient φ y)
  let q := planeEnergy A φ
  have hφ : PlaneSmooth φ := planeQuadraticWeight_smooth _ _ _ _
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq : PlaneSmooth q := planeEnergy_contDiff hA hφ
  have htrans : c<planeDrift b q a := by
    have hh := quadratic_weight_transport_lower hA hAs a hn hκ.le hε.le hℓ.le
      (by simpa only [hn,one_pow,mul_one] using hell n)
      (show ‖A a‖≤M by dsimp [M]; linarith)
      (show ‖fderiv ℝ A a‖≤K by dsimp [K]; linarith)
    change 2*κ*ℓ^2-2*ε*M^2-K*M≤planeDrift b q a at hh
    linarith
  let D := |planeElliptic A (planeDivergence b) a|+1
  have hD : 0≤D := by dsimp [D]; positivity
  have hDA := hA.continuous_fderiv (by simp)
  have hevM : ∀ᶠ x in 𝓝 a,‖A x‖<M :=
    (hA.continuous.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevK : ∀ᶠ x in 𝓝 a,‖fderiv ℝ A x‖<K :=
    (hDA.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevp : ∀ᶠ x in 𝓝 a,‖gradient φ x‖<2 :=
    ((plane_gradient_contDiff hφ).continuous.norm.tendsto a).eventually
      (eventually_lt_nhds (by simp only [φ,planeQuadraticWeight_gradient_center,hn]; norm_num))
  have hevell : ∀ᶠ x in 𝓝 a,‖A x-A a‖<ℓ/2 :=
    ((hA.continuous.sub continuous_const).norm.tendsto a).eventually
      (eventually_lt_nhds (by change ‖A a-A a‖<ℓ/2; simp only [sub_self,norm_zero]; positivity))
  have hevt : ∀ᶠ x in 𝓝 a,c<planeDrift b q x :=
    ((planeDrift_contDiff hb hq).continuous.tendsto a).eventually (eventually_gt_nhds htrans)
  have hevd : ∀ᶠ x in 𝓝 a,planeElliptic A (planeDivergence b) x<D :=
    ((planeElliptic_contDiff hA (planeDivergence_contDiff hb)).continuous.tendsto a).eventually
      (eventually_lt_nhds (by dsimp [D]; linarith [le_abs_self (planeElliptic A (planeDivergence b) a)]))
  have hev := hevM.and (hevK.and (hevp.and (hevell.and (hevt.and hevd))))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hell' (x : Plane) (hx : x∈Metric.ball a r) (v : Plane) :
      (ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
    have hh := plane_ellipticity_perturb hell (hball hx).2.2.2.1.le v
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨κ,hκ,r,hr,C,D,Q,c,?_,hell'⟩
  refine ⟨hC,hD,?_,?_,?_,?_,?_⟩
  · dsimp [c]
    linarith
  · intro x hx v
    obtain ⟨hMx,hKx,hpx,_,_,_⟩ := hball hx
    have hh := quadratic_weight_R_lower hA hAs a n hκ.le hε.le hMx.le hKx.le hpx.le v
    have hmul := mul_le_mul_of_nonneg_left (hell' x hx v) hC
    have hCB : C*(ℓ/2)=B := by dsimp [C]; exact div_mul_cancel₀ _ (by positivity)
    change -C*⟪v,A x v⟫≤planeCarlemanR A b x v
    have he : (4*ε*M^2+6*K*M*2)=B := by dsimp [B]; ring
    rw [he] at hh
    dsimp only [φ,b]
    nlinarith only [hh,hmul,hCB]
  · intro x hx
    obtain ⟨hMx,_,hpx,_,_,_⟩ := hball hx
    have hh := plane_inner_clm_bound (A x) (gradient φ x) (gradient φ x)
    change ⟪gradient φ x,A x (gradient φ x)⟫≤Q
    calc
      _ ≤ |⟪gradient φ x,A x (gradient φ x)⟫| := le_abs_self _
      _ ≤ ‖gradient φ x‖*‖A x‖*‖gradient φ x‖ := hh
      _ ≤ 2*M*2 := by gcongr
      _ = Q := by dsimp [Q]; ring
  · intro x hx
    exact (hball hx).2.2.2.2.1.le
  · intro x hx
    exact (hball hx).2.2.2.2.2.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quadratic_weight_scalar_outside {s t κ ε R : ℝ} (hR : 0<R) (ht : 0≤t)
    (hκ : 0≤κ) (hsmall : κ*t≤1) (hst : |s|≤t)
    (hout : 2*R*s≤t^2) (hε : 4/R≤ε) :
    s+(κ/2)*s^2-(ε/2)*t^2≤ -(1/R)*t^2 := by
  have hlin : s+(κ/2)*s^2≤t^2/R := by
    by_cases hs : s≤0
    · have hst' : -s≤t := by simpa only [abs_of_nonpos hs] using hst
      have hsκ : κ*(-s)≤1 :=
        (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ (neg_nonneg.mpr hs)
      have hn : 0≤t^2/R := div_nonneg (pow_nonneg ht 2) hR.le
      nlinarith only [hh,hn,hs]
    · have hs0 : 0≤ s := le_of_not_ge hs
      have hst' : s≤t := (le_abs_self _).trans hst
      have hsκ : κ*s≤1 := (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ hs0
      have hhout : 2*s≤t^2/R := (le_div_iff₀ hR).mpr (by nlinarith only [hout])
      nlinarith only [hh,hhout,hs0]
  have he := mul_le_mul_of_nonneg_right hε (sq_nonneg t)
  have heq₁ : (4/R)*t^2=4*(t^2/R) := by ring
  have heq₂ : -(1/R)*t^2= -(t^2/R) := by ring
  rw [heq₁] at he
  rw [heq₂]
  nlinarith only [he,hlin]

lemma planeQuadraticWeight_outside {a n x : Plane} {κ ε R : ℝ}
    (hn : ‖n‖=1) (hR : 0<R) (hκ : 0≤κ) (hsmall : κ*‖x-a‖≤1)
    (hout : R≤‖x-(a+R • n)‖) (hε : 4/R≤ε) :
    planeQuadraticWeight a n κ ε x≤ -(1/R)*‖x-a‖^2 := by
  have hst : |⟪n,x-a⟫|≤‖x-a‖ := by
    simpa only [hn,one_mul] using abs_real_inner_le_norm n (x-a)
  have he : ‖x-(a+R • n)‖^2=‖x-a‖^2+R^2-2*R*⟪n,x-a⟫ := by
    rw [show x-(a+R • n)=(x-a)-R • n by abel,norm_sub_sq_real]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hn,mul_one,real_inner_smul_right,
      real_inner_comm (x-a) n]
    ring
  have hout' : 2*R*⟪n,x-a⟫≤‖x-a‖^2 := by
    have hh := sq_le_sq₀ hR.le (norm_nonneg _) |>.mpr hout
    rw [he] at hh
    linarith
  exact quadratic_weight_scalar_outside hR (norm_nonneg _) hκ hsmall hst hout' hε

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_exp {f : Plane → ℝ} (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    gradient (fun y => Real.exp (τ*f y)) x=(τ*Real.exp (τ*f x)) • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma planeElliptic_mul {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (hg : PlaneSmooth g)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeElliptic A (fun y => f y*g y) x=
      f x*planeElliptic A g x+g x*planeElliptic A f x+2*⟪gradient f x,A x (gradient g x)⟫ := by
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hG := hA.clm_apply (plane_gradient_contDiff hg)
  have he : (fun y => A y (gradient (fun z => f z*g z) y))=
      fun y => f y • A y (gradient g y)+g y • A y (gradient f y) := by
    funext y
    rw [plane_gradient_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp only [map_add,map_smul]
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_add ((hf.smul hG).differentiable (by simp) x)
      ((hg.smul hF).differentiable (by simp) x),
    planeDivergence_smul (hf.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hg.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [hAs x (gradient g x) (gradient f x)]
  ring

lemma planeElliptic_exp {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    planeElliptic A (fun y => Real.exp (τ*f y)) x=
      Real.exp (τ*f x)*(τ*planeElliptic A f x+τ^2*planeEnergy A f x) := by
  have he : (fun y => A y (gradient (fun z => Real.exp (τ*f z)) y))=
      fun y => (τ*Real.exp (τ*f y)) • A y (gradient f y) := by
    funext y
    rw [plane_gradient_exp hf,map_smul]
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hk : PlaneSmooth (fun y => τ*Real.exp (τ*f y)) :=
    contDiff_const.mul ((contDiff_const.mul hf).exp)
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_smul (hk.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [inner_gradient_left,fderiv_const_mul (((contDiff_const.mul hf).exp).differentiable (by simp) x)]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul,← inner_gradient_left,planeEnergy]
  ring

theorem planeCarleman_conjugation {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫) (τ : ℝ) (x : Plane) :
    planeCarlemanP A (fun y => A y (gradient φ y)) (planeEnergy A φ) τ
      (fun y => Real.exp (τ*φ y)*v y) x=Real.exp (τ*φ x)*planeElliptic A v x := by
  have he : PlaneSmooth (fun y => Real.exp (τ*φ y)) := (contDiff_const.mul hφ).exp
  unfold planeCarlemanP planeCarlemanS planeCarlemanT planeDrift
  rw [planeElliptic_mul hA he hv hAs,planeElliptic_exp hA hφ,plane_gradient_exp hφ,
    fderiv_fun_mul (he.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  rw [(((hφ.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,← inner_gradient_left,real_inner_smul_left,
    planeEnergy,planeElliptic]
  rw [hAs x (gradient v x) (gradient φ x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_square_compact {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (fun x => u x^2) := hc.mono (by
  intro x hx hz
  exact hx (by simp [hz]))

theorem planeCarleman_weighted {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    τ^3*(∫ x,(Real.exp (τ*φ x))^2*v x^2)≤
      ∫ x,(Real.exp (τ*φ x))^2*(planeElliptic A v x)^2 := by
  let u : Plane → ℝ := fun x => Real.exp (τ*φ x)*v x
  have hu : PlaneSmooth u := ((contDiff_const.mul hφ).exp).mul hv
  have huc : HasCompactSupport u := hc.mul_left
  have hus : tsupport u⊆tsupport v := tsupport_mul_subset_right
  have hb := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq := planeEnergy_contDiff hA hφ
  have he := planeCarleman_coercive hA hb hq hu huc hAs (hus.trans hs) hdata hτ hbudget
  have hn (x : Plane) : 0≤planeEnergy A u x := by
    by_cases hx : x∈tsupport u
    · exact hell x (hs (hus hx)) (gradient u x)
    · have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp [planeEnergy,hg]
  have hi : Integrable (fun x => τ^3*u x^2) :=
    (((hu.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact huc)).const_mul _)
  have hj : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact huc)).const_mul τ).add hi
  have hm := integral_mono hi hj (fun x => le_add_of_nonneg_left (mul_nonneg (by linarith) (hn x)))
  have ht := hm.trans he
  simp only [u,planeCarleman_conjugation hA hφ hv hAs,mul_pow] at ht
  rwa [integral_const_mul] at ht

theorem planeCarleman_vanish_above {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c d : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hres : ∀ x,planeElliptic A v x≠0 → φ x≤d) :
    ∀ x,d<φ x → v x=0 := by
  let S : Set Plane := {x | d<φ x}
  have hSo : IsOpen S := isOpen_lt continuous_const hφ.continuous
  have hSm : MeasurableSet S := hSo.measurableSet
  have hvI : Integrable (fun x => v x^2) :=
    (hv.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hc)
  have hL := planeElliptic_contDiff hA hv
  have hLc := planeElliptic_compact (A := A) hc
  have hLI : Integrable (fun x => planeElliptic A v x^2) :=
    (hL.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hLc)
  let I : ℝ := ∫ x in S,v x^2
  let N : ℝ := ∫ x,planeElliptic A v x^2
  have hI : 0≤I := integral_nonneg (fun _ => sq_nonneg _)
  have hN : 0≤N := integral_nonneg (fun _ => sq_nonneg _)
  have hbound (τ : ℝ) (ht : 1≤τ) (hb : D+(C+1)^2≤τ) : τ^3*I≤N := by
    have ht0 : 0≤τ := by linarith
    let w : Plane → ℝ := fun x => (Real.exp (τ*φ x))^2
    let W : ℝ := (Real.exp (τ*d))^2
    have hW : 0<W := sq_pos_of_pos (Real.exp_pos _)
    have hw : Continuous w := (Real.continuous_exp.comp (continuous_const.mul hφ.continuous)).pow 2
    have hi : Integrable (fun x => w x*v x^2) :=
      (hw.mul (hv.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hc).mul_left
    have hj : Integrable (fun x => w x*planeElliptic A v x^2) :=
      (hw.mul (hL.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hLc).mul_left
    have hlo : W*I≤∫ x,w x*v x^2 := by
      rw [← integral_const_mul,← integral_indicator hSm]
      apply integral_mono ((hvI.const_mul W).indicator hSm) hi
      intro x
      by_cases hx : x∈S
      · rw [indicator_of_mem hx]
        apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_of_lt hx) ht0)) 2
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hhi : (∫ x,w x*planeElliptic A v x^2)≤W*N := by
      rw [← integral_const_mul]
      apply integral_mono hj (hLI.const_mul W)
      intro x
      by_cases hx : planeElliptic A v x=0
      · simp [hx]
      · apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hres x hx) ht0)) 2
    have hh := planeCarleman_weighted hA hφ hv hc hAs hs hell hdata ht hb
    have hmul := mul_le_mul_of_nonneg_left hlo (pow_nonneg ht0 3)
    have hf : W*(τ^3*I)≤W*N := by nlinarith only [hmul,hh,hhi]
    nlinarith only [hf,hW]
  have hIz : I=0 := by
    by_contra hz
    have hip : 0<I := lt_of_le_of_ne hI (Ne.symm hz)
    let τ := max 1 (max (D+(C+1)^2) (N/I+1))
    have ht : 1≤τ := le_max_left _ _
    have hb : D+(C+1)^2≤τ := (le_max_left _ _).trans (le_max_right _ _)
    have hlarge : N/I+1≤τ := (le_max_right _ _).trans (le_max_right _ _)
    have hτI : N<τ*I := by
      have hx := (div_lt_iff₀ hip).mp (show N/I<τ by linarith)
      linarith
    have hpow : τ≤τ^3 := by nlinarith [sq_nonneg (τ-1)]
    have hp := mul_le_mul_of_nonneg_right hpow hI
    linarith [hbound τ ht hb]
  have hae : (fun x => v x^2)=ᵐ[volume.restrict S] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun x => sq_nonneg (v x)))
      hvI.integrableOn).mp hIz
  have heq := Measure.eqOn_open_of_ae_eq hae hSo (hv.continuous.pow 2).continuousOn continuousOn_const
  intro x hx
  have hz := heq hx
  exact sq_eq_zero_iff.mp hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f=ᶠ[𝓝 x] g) : gradient f=ᶠ[𝓝 x] gradient g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [gradient,hy]

lemma planeElliptic_congr_nhds {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    {x : Plane} (h : f=ᶠ[𝓝 x] g) : planeElliptic A f x=planeElliptic A g x := by
  have hg : (fun y => A y (gradient f y))=ᶠ[𝓝 x] (fun y => A y (gradient g y)) := by
    filter_upwards [plane_gradient_eventuallyEq h] with y hy
    rw [hy]
  simp only [planeElliptic,planeDivergence,hg.fderiv_eq]

lemma planeElliptic_zero_of_notMem_tsupport {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {x : Plane} (hx : x∉tsupport f) : planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

lemma planeElliptic_zero_on_open {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hz : ∀ x∈U,f x=0) {x : Plane} (hx : x∈U) :
    planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planeElliptic_continue_tangent_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a n : Plane} (ha : a∈U) (hn : ‖n‖=1)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball (a+R • n) R,f x=0) :
    a∈interior {x | f x=0} := by
  obtain ⟨κ,hκ,r₀,hr₀,C,D,Q,c,hdata,hell'⟩ :=
    planeCarleman_weight_exists hA hAs a hn hℓ (show 0<4/R by positivity) hell
  obtain ⟨rU,hrU,hballU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min r₀ (min rU (1/(κ+1)))
  have hr : 0 < r := lt_min hr₀ (lt_min hrU (by positivity))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrrU : r ≤ rU := (min_le_left _ _).trans' (min_le_right _ _)
  have hrrκ : r≤1/(κ+1) := (min_le_right _ _).trans (min_le_right _ _)
  let χ : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let v : Plane → ℝ := fun x => χ x*f x
  let φ := planeQuadraticWeight a n κ (4/R)
  let d := -(1/R)*(r/4)^2
  have hv : PlaneSmooth v := χ.contDiff.mul hf
  have hvc : HasCompactSupport v := χ.hasCompactSupport.mul_right
  have hvs : tsupport v⊆Metric.closedBall a (r/2) := by
    calc tsupport v ⊆ tsupport (χ : Plane → ℝ) := tsupport_mul_subset_left
         _ = _ := χ.tsupport_eq
  have hs₀ : tsupport v⊆Metric.ball a r₀ := by
    intro x hx
    have hh : dist x a ≤ r/2 := hvs hx
    change dist x a < r₀
    linarith
  have hsU : tsupport v⊆U := by
    intro x hx
    apply hballU
    have hh : dist x a ≤ r/2 := hvs hx
    change dist x a < rU
    linarith
  have hveq {x : Plane} (hx : x∈Metric.ball a (r/4)) : v=ᶠ[𝓝 x] f := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with y hy
    change χ y*f y=f y
    simp only [hy,Pi.one_apply,one_mul]
  have hres (x : Plane) (hx : planeElliptic A v x≠0) : φ x≤d := by
    have hxs : x∈tsupport v := by
      by_contra h
      exact hx (planeElliptic_zero_of_notMem_tsupport h)
    have hsmall : κ*‖x-a‖≤1 := by
      have hdist : ‖x-a‖ ≤ r/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hvs hxs
      have hk : κ*r≤1 := by
        have hb := (le_div_iff₀ (show 0<κ+1 by positivity)).mp hrrκ
        nlinarith
      nlinarith
    have hout : R≤‖x-(a+R • n)‖ := by
      by_contra h
      have hxin : x∈Metric.ball (a+R • n) R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      apply hx
      apply planeElliptic_zero_on_open Metric.isOpen_ball (x := x) (hx := hxin)
      intro y hy
      dsimp [v]
      rw [hz y hy,mul_zero]
    have hfar : r/4≤‖x-a‖ := by
      by_contra h
      have hxin : x∈Metric.ball a (r/4) := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      exact hx ((planeElliptic_congr_nhds (hveq hxin)).trans (heq x (hsU hxs)))
    have hh := planeQuadraticWeight_outside hn hR hκ.le hsmall hout (le_refl (4/R))
    change φ x≤d
    apply hh.trans
    dsimp [d]
    have hsq : (r/4)^2≤‖x-a‖^2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hfar
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤1/R by positivity)]
  have hvan := planeCarleman_vanish_above hA (planeQuadraticWeight_smooth _ _ _ _)
    hv hvc hAs hs₀ (fun x hx w => (by positivity : 0≤(ℓ/2)*‖w‖^2).trans (hell' x hx w))
    hdata hres
  have hd : d<φ a := by
    dsimp [φ,planeQuadraticWeight,d]
    simp only [sub_self,inner_zero_right,zero_pow (by decide : 2≠0),mul_zero,norm_zero,
      zero_add]
    have hp : 0<(1/R)*(r/4)^2 := by positivity
    linarith
  have ho : IsOpen {x : Plane | d<φ x} :=
    isOpen_lt continuous_const (planeQuadraticWeight_smooth _ _ _ _).continuous
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (inter_mem (ho.mem_nhds hd)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (show 0 < r/4 by positivity))))
  intro x hx
  have hvz := hvan x hx.1
  have he := Filter.EventuallyEq.eq_of_nhds (hveq hx.2)
  exact he.symm.trans hvz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeHopfBarrier_smooth (c : Plane) (α R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeHopfBarrier c α R) :=
  ((contDiff_const.mul (((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => x)).sub contDiff_const).norm_sq ℝ)).exp).sub contDiff_const

lemma planeHopfBarrier_fderiv (c : Plane) (α R : ℝ) (x : Plane) :
    fderiv ℝ (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • innerSL ℝ (x-c) := by
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp.sub_const
    (Real.exp (-α*R^2))
  change fderiv ℝ (fun x => Real.exp (-α*‖x-c‖^2)-Real.exp (-α*R^2)) x=_
  simp only [id_eq] at h
  rw [h.fderiv]
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma planeHopfBarrier_gradient (c : Plane) (α R : ℝ) (x : Plane) :
    gradient (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • (x-c) := by
  ext i
  rw [plane_gradient_component,planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,smul_eq_mul,PiLp.smul_apply]

lemma planeHopfBarrier_hessian (c : Plane) (α R : ℝ) (x v : Plane) :
    ⟪fderiv ℝ (gradient (planeHopfBarrier c α R)) x v,v⟫=
      Real.exp (-α*‖x-c‖^2)*(4*α^2*⟪x-c,v⟫^2-2*α*‖v‖^2) := by
  have he : gradient (planeHopfBarrier c α R)=
      fun y => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c) :=
    funext (planeHopfBarrier_gradient c α R)
  rw [he]
  have hd := (((((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp).const_mul (-2*α)).smul
    ((hasFDerivAt_id x).sub_const c)
  simp only [id_eq] at hd
  change HasFDerivAt (fun y : Plane => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

lemma planeFrameOperator_barrier (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) (α R : ℝ) (x : Plane) :
    planeFrameOperator B b (planeHopfBarrier c α R) x=
      Real.exp (-α*‖x-c‖^2)*
        (4*α^2*(∑ i,⟪x-c,B x i⟫^2)-2*α*(∑ i,‖B x i‖^2)-2*α*⟪x-c,b x⟫) := by
  simp only [planeFrameOperator,planeHopfBarrier_hessian,planeHopfBarrier_gradient,
    real_inner_smul_left,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma planeFrameOperator_barrier_pos (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) {α R r κ K : ℝ} (hr : 0 < r) (hκ : 0<κ) (hK : 0≤K)
    (hα : 0<α) (hlarge : K*(1+R)<2*α*κ*r^2)
    {x : Plane} (hrx : r≤‖x-c‖) (hxR : ‖x-c‖≤R)
    (hell : κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2)
    (hB : (∑ i,‖B x i‖^2)≤K) (hb : ‖b x‖≤K) :
    0<planeFrameOperator B b (planeHopfBarrier c α R) x := by
  rw [planeFrameOperator_barrier]
  apply mul_pos (Real.exp_pos _) ?_
  have hb' : ⟪x-c,b x⟫≤R*K := (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hxR hK))
  have hsq : r^2≤‖x-c‖^2 := sq_le_sq₀ hr.le (norm_nonneg _) |>.mpr hrx
  have he : κ*r^2≤∑ i,⟪x-c,B x i⟫^2 :=
    (mul_le_mul_of_nonneg_left hsq hκ.le).trans hell
  have ha2 : 0<2*α := by positivity
  have ha4 : 0≤4*α^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left he ha4
  have h2 := mul_le_mul_of_nonneg_left hB ha2.le
  have h3 := mul_le_mul_of_nonneg_left hb' ha2.le
  have h4 := mul_lt_mul_of_pos_left hlarge ha2
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma deriv_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),f 0≤f t) : 0≤d := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  apply ge_of_tendsto ht
  filter_upwards [hm,self_mem_nhdsWithin] with t hmt ht
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr hmt) (by simpa using (show 0≤t from le_of_lt ht))

lemma planeHopfBarrier_inward (c : Plane) {α R : ℝ} (hα : 0<α) (hR : 0<R)
    {y : Plane} (hy : ‖y-c‖=R) :
    0<fderiv ℝ (planeHopfBarrier c α R) y (c-y) := by
  rw [planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul]
  have hi : ⟪y-c,c-y⟫= -R^2 := by
    rw [show c-y= -(y-c) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hy]
  rw [hi]
  have hp : 0<2*α*Real.exp (-α*‖y-c‖^2)*R^2 := by positivity
  nlinarith

theorem planeFrameOperator_hopf (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (c : Plane) {R κ K : ℝ} (hR : 0<R) (hκ : 0<κ) (hK : 0≤K)
    (hcoeff : ∀ x,R/2≤‖x-c‖ → ‖x-c‖≤R →
      κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2 ∧
        (∑ i,‖B x i‖^2)≤K ∧ ‖b x‖≤K)
    (hL : ∀ x,‖x-c‖<R → planeFrameOperator B b u x≤0)
    (hpos : ∀ x,‖x-c‖<R → 0<u x)
    {y : Plane} (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrR : r<R := half_lt_self hR
  have hbound : ∀ x,‖x-c‖≤R → 0≤u x := by
    have hs : Metric.ball c R⊆{x | 0≤u x} := by
      intro x hx
      exact (hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)).le
    have hc := closure_minimal hs (isClosed_le continuous_const hu.continuous)
    rw [closure_ball c hR.ne'] at hc
    intro x hx
    exact hc (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  obtain ⟨z,hz,hzmin⟩ := (isCompact_closedBall c r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) hu.continuous.continuousOn
  have hzr : ‖z-c‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  let δ := u z
  have hδ : 0<δ := hpos z (hzr.trans_lt hrR)
  let α := (K*(1+R)+1)/(2*κ*r^2)
  have hα : 0<α := by dsimp [α]; positivity
  have hlarge : K*(1+R)<2*α*κ*r^2 := by
    have he : 2*α*κ*r^2=K*(1+R)+1 := by
      dsimp [α]; field_simp
    rw [he]; linarith
  let φ := planeHopfBarrier c α R
  have hφ := planeHopfBarrier_smooth c α R
  have hφle (x : Plane) : φ x≤1 := by
    have he : Real.exp (-α*‖x-c‖^2)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (sq_nonneg _))
    dsimp [φ,planeHopfBarrier]
    linarith [Real.exp_pos (-α*R^2)]
  have hφzero (x : Plane) (hx : ‖x-c‖=R) : φ x=0 := by simp only [φ,planeHopfBarrier,hx,sub_self]
  have hcomp : ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤u x-δ*φ x := by
    apply planeFrameOperator_annulus_comparison B b (hu.sub (contDiff_const.mul hφ)) c hr hrR
    · intro x hx
      change 0≤u x-δ*φ x
      rcases hx with hx|hx
      · have hzle : δ≤u x := hzmin (by simpa only [Metric.mem_closedBall,dist_eq_norm,hx] using (le_refl r))
        have hh := mul_le_mul_of_nonneg_left (hφle x) hδ.le
        nlinarith
      · rw [hφzero x hx,mul_zero,sub_zero]
        exact hbound x hx.le
    · intro x hrx hxR
      rw [planeFrameOperator_sub B b hu (contDiff_const.mul hφ),
        planeFrameOperator_smul B b hφ]
      have hc := hcoeff x hrx.le hxR.le
      have hbar := planeFrameOperator_barrier_pos B b c hr hκ hK hα hlarge
        hrx.le hxR.le hc.1 hc.2.1 hc.2.2
      exact sub_neg.mpr ((hL x hxR).trans_lt (mul_pos hδ hbar))
  let g : ℝ → ℝ := fun t => u (y+t • (c-y))-δ*φ (y+t • (c-y))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (hu.sub (contDiff_const.mul hφ)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg0 : g 0=0 := by simp only [g,zero_smul,add_zero,huy,hφzero y hy,mul_zero,sub_self]
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),g 0≤g t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with t ht hth
    have ht0 : 0<t := ht
    have hnorm : ‖y+t • (c-y)-c‖=(1-t)*R := by
      rw [show y+t • (c-y)-c=(1-t) • (y-c) by module,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith),hy]
    rw [hg0]
    apply hcomp
    · rw [hnorm]; dsimp [r]; nlinarith
    · rw [hnorm]; nlinarith
  have hd := deriv_nonneg_of_right_min (hg.differentiable (by simp) 0).hasDerivAt hm
  have he : deriv g 0=fderiv ℝ u y (c-y)-δ*fderiv ℝ φ y (c-y) := by
    have hl := smooth_line_deriv (hu.sub ((contDiff_const (c := δ)).mul hφ)) y (c-y) 0
    change deriv g 0=_ at hl
    rw [hl]
    simp only [zero_smul,add_zero]
    rw [fderiv_fun_sub (hu.differentiable (by simp) y)
      ((contDiff_const.mul hφ).differentiable (by simp) y),
      fderiv_const_mul (hφ.differentiable (by simp) y)]
    simp [φ]

  rw [he] at hd
  exact (mul_pos hδ (planeHopfBarrier_inward c hα hR hy)).trans_le (sub_nonneg.mp hd)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CMCFrameOperator
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

theorem plane_interior_ball_at_frontier {D : Set Plane} (hD : IsOpen D)
    {a : Plane} (ha : a∈frontier D) {ε : ℝ} (hε : 0<ε) :
    ∃ (c y : Plane) (R : ℝ),0<R ∧
      Metric.ball c R⊆D ∧ ‖y-c‖=R ∧ y∈frontier D ∧
      Metric.closedBall c R⊆Metric.ball a ε := by
  have hac : a∈closure D := frontier_subset_closure ha
  have had : a∉D := by
    rw [frontier, hD.interior_eq] at ha
    exact ha.2
  obtain ⟨c,hcD,hca⟩ := Metric.mem_closure_iff.mp hac (ε/4) (by positivity)
  have hcomp : Dᶜ.Nonempty := ⟨a,had⟩
  let R := Metric.infDist c Dᶜ
  have hR : 0<R := (hD.isClosed_compl.notMem_iff_infDist_pos hcomp).mp (by simpa using hcD)
  have hRa : R≤dist c a := Metric.infDist_le_dist_of_mem had
  obtain ⟨y,hyc,hRy⟩ := hD.isClosed_compl.exists_infDist_eq_dist hcomp c
  have hball : Metric.ball c R⊆D := Metric.ball_infDist_compl_subset
  have hyR : ‖y-c‖=R := by
    rw [← dist_eq_norm,dist_comm]
    exact hRy.symm
  have hycl : y∈closure D := by
    apply closure_mono hball
    rw [closure_ball c hR.ne']
    simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)
  refine ⟨c,y,R,hR,hball,hyR,?_,?_⟩
  · rw [frontier,hD.interior_eq]
    exact ⟨hycl,hyc⟩
  · intro z hz
    have hzR : dist z c≤R := hz
    have hca' : dist c a<ε/4 := by simpa only [dist_comm] using hca
    have hza := dist_triangle z c a
    change dist z a<ε
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeElliptic_continue_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a c : Plane} (ha : a∈U)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R) (hd : ‖a-c‖=R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball c R,f x=0) :
    a∈interior {x | f x=0} := by
  let n : Plane := (1/R) • (c-a)
  have hn : ‖n‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<1/R by positivity),norm_sub_rev,hd]
    exact one_div_mul_cancel hR.ne'
  have hc : a+R • n=c := by
    dsimp [n]
    rw [smul_smul,mul_one_div_cancel hR.ne',one_smul]
    abel
  exact planeElliptic_continue_tangent_ball hA hf hAs hU ha hn hℓ hR hell heq (by simpa [hc] using hz)

theorem planeElliptic_unique_continuation {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hell : ∀ x∈U,∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,A x v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hpatch : (U∩interior {x | f x=0}).Nonempty) :
    ∀ x∈U,f x=0 := by
  let D := interior {x | f x=0}
  have hD : IsOpen D := isOpen_interior
  have hno : Disjoint (frontier D) U := by
    rw [Set.disjoint_left]
    intro a ha haU
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a haU
    obtain ⟨c,y,R,hR,hball,hyR,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
    have hyU : y∈U := hεU (hsub (by
      simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)))
    obtain ⟨ℓ,hℓ,hell⟩ := hell y hyU
    have hyz := planeElliptic_continue_ball hA hf hAs hU hyU hℓ hR hyR hell heq
      (fun x hx => show x∈{y | f y=0} from interior_subset (hball hx))
    have hyn : y∉D := by
      rw [frontier,hD.interior_eq] at hyD
      exact hyD.2
    exact hyn hyz
  have hsub : U⊆D := hUc.subset_of_closure_inter_subset hD hpatch (by
    intro x hx
    by_contra hn
    apply Set.disjoint_left.mp hno ?_ hx.2
    rw [frontier,hD.interior_eq]
    exact ⟨hx.1,hn⟩)
  exact fun x hx => show x∈{y | f y=0} from interior_subset (hsub hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_symbol {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) {u : Plane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeDivergence (fun z => A z (gradient u z)) x=
      planeTrace ((A x).comp (fderiv ℝ (gradient u) x))+
        ⟪gradient u x,planeSymbolDrift A x⟫ := by
  have hda := (hA.differentiable (by simp) x).hasFDerivAt
  have hdu := ((plane_gradient_contDiff hu).differentiable (by simp) x).hasFDerivAt
  have hprod := hda.clm_apply hdu
  have hc (j : Fin 2) := hda.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  simp only [planeSymbolDrift,planeDivergence,planeTrace]
  rw [hprod.fderiv]
  simp_rw [(hc _).fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_zero,
    Fin.sum_univ_two,inner_add_right,real_inner_smul_right,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.add_apply]
  rw [plane_decompose (gradient u x)]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    PiLp.single_apply,ite_true,mul_one]
  norm_num
  ring

lemma cmc_compress_hessian_trace (p : Plane) (L : Plane →L[ℝ] Plane) :
    (∑ i : Fin 2,⟪L (cmcCompress p (EuclideanSpace.single i 1)),
      cmcCompress p (EuclideanSpace.single i 1)⟫)=
      cmcWeight p*planeTrace ((cmcJacobian p).comp L) := by
  calc
    _ = planeTrace ((cmcCompress p).comp (L.comp (cmcCompress p))) := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,← cmcCompress_symm,
        EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    _ = planeTrace ((L.comp (cmcCompress p)).comp (cmcCompress p)) := planeTrace_comp_comm _ _
    _ = planeTrace (L.comp ((cmcCompress p).comp (cmcCompress p))) := by rfl
    _ = planeTrace (((cmcCompress p).comp (cmcCompress p)).comp L) := planeTrace_comp_comm _ _
    _ = _ := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,cmcCompress_sq,PiLp.smul_apply,
        smul_eq_mul,← Finset.mul_sum]

lemma cmc_frame_operator {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeFrameOperator (fun y i => cmcCompress (gradient g y) (EuclideanSpace.single i 1))
      (fun y => cmcWeight (gradient g y) •
        planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x=
      cmcWeight (gradient g x)*planeDivergence
        (fun y => cmcJacobian (gradient g y) (gradient u y)) x := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z => cmcJacobian (gradient g z)) :=
    cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  rw [planeDivergence_symbol hA hu]
  simp only [planeFrameOperator,cmc_compress_hessian_trace,real_inner_smul_right]
  ring

lemma cmc_frame_ellipticity {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/4 : ℝ)*‖v‖^2≤∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2 := by
  have he : (∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2)=‖cmcCompress p v‖^2 := by
    simp only [← cmcCompress_symm,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [he]
  have hh := cmcStretch_norm hp (cmcCompress p v)
  rw [cmcStretch_compress] at hh
  nlinarith [norm_nonneg (cmcCompress p v),norm_nonneg v]

lemma cmc_frame_bound {p : Plane} (hp : ‖p‖≤1) :
    (∑ i : Fin 2,‖cmcCompress p (EuclideanSpace.single i 1)‖^2)≤8 := by
  have hh (i : Fin 2) : ‖cmcCompress p (EuclideanSpace.single i 1)‖≤2 := by
    simpa using cmcCompress_norm hp (EuclideanSpace.single i 1)
  rw [Fin.sum_univ_two]
  nlinarith [hh 0,hh 1,norm_nonneg (cmcCompress p (EuclideanSpace.single 0 1)),
    norm_nonneg (cmcCompress p (EuclideanSpace.single 1 1))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeSymbolDrift_continuous {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) : Continuous (planeSymbolDrift A) := by
  unfold planeSymbolDrift
  apply continuous_finsetSum
  intro i _
  exact (planeDivergence_continuous ((hA.clm_apply contDiff_const).of_le (by simp))).smul continuous_const

theorem LinearCMCEquation.hopf {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R : ℝ} (hR : 0<R)
    (hp : ∀ x∈Metric.closedBall c R,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball c R))
    (hpos : ∀ x∈Metric.ball c R,0<u x)
    (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let A : Plane → Plane →L[ℝ] Plane := fun x => cmcJacobian (gradient g x)
  let b : Plane → Plane := fun x => cmcWeight (gradient g x) • planeSymbolDrift A x
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  have hb : Continuous b := (cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).continuous.smul
    (planeSymbolDrift_continuous hA)
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hb.continuousOn
  let K := max 8 (max C 0)
  have hK8 : 8≤K := le_max_left _ _
  have hKC : C≤K := (le_max_left C 0).trans (le_max_right _ _)
  have hK : 0≤K := (le_max_right C 0).trans (le_max_right _ _)
  apply planeFrameOperator_hopf
    (fun x i => cmcCompress (gradient g x) (EuclideanSpace.single i 1)) b hu c hR
    (by norm_num : 0<(1/4 : ℝ)) hK ?_ ?_ ?_ hy huy
  · intro x _ hxR
    have hx : x∈Metric.closedBall c R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hxR
    exact ⟨cmc_frame_ellipticity (hp x hx) (x-c),
      (cmc_frame_bound (hp x hx)).trans hK8,(hC x hx).trans hKC⟩
  · intro x hx
    change planeFrameOperator _ (fun y => cmcWeight (gradient g y) •
      planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x≤0
    rw [cmc_frame_operator hg hu,hw.classical_zero hg hu Metric.isOpen_ball x
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hx),mul_zero]
  · intro x hx
    exact hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_strict_coercive (p v : Plane) :
    (1/(cmcWeight p)^3)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  rw [cmcJacobian_self]
  have hp := cmcWeight_pos p
  have hw := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  rw [one_div_mul_eq_div,div_le_div_iff_of_pos_right (by positivity : 0<(cmcWeight p)^3)]
  nlinarith

theorem LinearCMCEquation.unique_continuation {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) U)
    (hpatch : (U∩interior {x | u x=0}).Nonempty) : ∀ x∈U,u x=0 := by
  exact planeElliptic_unique_continuation (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)) hu
    (fun x v w => (cmcJacobian_symmetric _ _ _).trans (real_inner_comm _ _)) hU hUc
    (fun x _ => ⟨1/(cmcWeight (gradient g x))^3,by have hh := cmcWeight_pos (gradient g x); positivity,cmcJacobian_strict_coercive _⟩)
    (hw.classical_zero hg hu hU) hpatch

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.affine_zero {u v : Plane → ℝ} {p : Plane → Plane}
    {U : Set Plane} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : Continuous p)
    (hue : LinearCMCEquation u p (fun _ => 0) U)
    (hve : LinearCMCEquation v p (fun _ => 0) U) (c a b : ℝ) :
    LinearCMCEquation (fun y => c+a*u y+b*v y) p (fun _ => 0) U := by
  have hg (y : Plane) : gradient (fun z => c+a*u z+b*v z) y=
      a • gradient u y+b • gradient v y := by
    have hd := ((hasFDerivAt_const c y).add
      ((hu.differentiable (by simp) y).hasFDerivAt.const_mul a)).add
        ((hv.differentiable (by simp) y).hasFDerivAt.const_mul b)
    have he : fderiv ℝ (fun z => c+a*u z+b*v z) y=
        0+a • fderiv ℝ u y+b • fderiv ℝ v y := hd.fderiv
    simp only [gradient,he,zero_add,map_add,map_smul]
  intro ψ hψ hc hs
  have hi (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
      Integrable (fun y => fderiv ℝ ψ y (cmcJacobian (p y) (gradient w y))) := by
    apply ((hψ.continuous_fderiv (by simp)).clm_apply
      ((cmcJacobian_contDiff.continuous.comp hp).clm_apply
        (plane_gradient_contDiff hw).continuous)).integrable_of_hasCompactSupport
    apply (hc.fderiv ℝ).mono
    intro y hy hz
    exact hy (by simp only [hz,zero_apply])
  simp_rw [hg,sub_zero,map_add,map_smul,smul_eq_mul]
  rw [integral_add ((hi u hu).const_mul a) ((hi v hv).const_mul b),
    integral_const_mul,integral_const_mul]
  have hu0 := hue ψ hψ hc hs
  have hv0 := hve ψ hψ hc hs
  simp only [sub_zero] at hu0 hv0
  rw [hu0,hv0,mul_zero,mul_zero,add_zero]

lemma normalTranslationNumerator_contDiff (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalTranslationNumerator n g v σ) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_const.inner ℝ (plane_gradient_contDiff hg)))

lemma normalTranslationNumerator_eq (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : normalTranslationNumerator n g v σ y=
      σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
        fderiv ℝ g y (EuclideanSpace.single 0 1)+
      (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1) := by
  simp only [normalTranslationNumerator,plane_inner_components,plane_gradient_component]
  ring

lemma normalTranslationNumerator_linear (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) {U : Set Plane}
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) U) :
    LinearCMCEquation (normalTranslationNumerator n g v σ) (gradient g) (fun _ => 0) U := by
  simp_rw [show normalTranslationNumerator n g v σ = fun y =>
    σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
      fderiv ℝ g y (EuclideanSpace.single 0 1)+
    (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1)
      from funext (normalTranslationNumerator_eq n g v σ)]
  exact (hlin 0).affine_zero
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    (plane_gradient_contDiff hg).continuous (hlin 1) _ _ _

lemma normalTranslationNumerator_weight {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (v : Cover) (σ : ℝ) (y : Plane) :
    normalTranslationNumerator n g v σ y=
      cmcWeight (gradient g y)*⟪v,σ • graphSlopeNormal n (gradient g y)⟫ := by
  rw [graphSlopeNormal_weight hn]
  simp only [normalTranslationNumerator,inner_smul_right,inner_sub_right]
  have he : ⟪normalPlaneCoordinates n v,gradient g y⟫=
      ⟪v,normalPlaneEmbedding n (gradient g y)⟫ :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [he]
  field_simp [(cmcWeight_pos (gradient g y)).ne']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotient_graph_closure {S D : Set Torus} (hDS : D⊆S)
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hx : quotientMap x∈closure D) :
    (0 : Plane)∈closure ((fun y => quotientMap (x+G y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball (0 : Plane) ε := by
    have ht : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
      simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
    exact ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hcover.and hP)
  obtain ⟨a,haD,hax⟩ := Metric.mem_closure_iff.mp hx δ hδ
  have ha : a∈Metric.ball (quotientMap x) δ := by
    simpa only [Metric.mem_ball,dist_comm] using hax
  rw [← quotientMap_image_ball x δ] at ha
  obtain ⟨z,hzx,hza⟩ := ha
  have hz : z-x∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hzx
  obtain ⟨hi,hp⟩ := hsub hz
  have hzs : quotientMap (x+(z-x))∈S := by
    simpa only [add_sub_cancel,hza] using hDS haD
  refine ⟨P (z-x),?_,?_⟩
  · change quotientMap (x+G (P (z-x)))∈D
    rw [hi hzs,add_sub_cancel,hza]
    exact haD
  · simpa only [Metric.mem_ball,dist_comm] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma relativeZeroNeighborhood_zero {S : Set Torus} {F : Torus → ℝ} {a : Torus}
    (ha : a∈S) (hz : a∈relativeZeroNeighborhood S F) : F a=0 := by
  have h : a∈Sᶜ∪{a | F a=0} := interior_subset hz
  exact h.resolve_left (fun hn => hn ha)

lemma quotient_graph_zero_germ {S : Set Torus} {F : Torus → ℝ}
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),F (quotientMap (x+G y))=0) :
    quotientMap x∈relativeZeroNeighborhood S F := by
  have hP : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
  have hev : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → F (quotientMap (x+v))=0 := by
    filter_upwards [hcover,hP.eventually hz] with v hv hvz hS
    rwa [hv hS] at hvz
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  change quotientMap x∈interior (Sᶜ∪{a | F a=0})
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (quotientMap x) hδ)
  intro a ha
  by_cases haS : a∈S
  · right
    rw [← quotientMap_image_ball x δ] at ha
    obtain ⟨z,hz,hza⟩ := ha
    have hz' : z-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
    have hh := hball hz'
    change F a=0
    simpa only [add_sub_cancel,hza] using hh (by simpa only [add_sub_cancel,hza] using haS)
  · exact Or.inl haS

lemma preconnected_zero_of_closed_germ {S : Set Torus} {F : Torus → ℝ}
    (hS : IsPreconnected S) (hD : IsClosed (S∩relativeZeroNeighborhood S F))
    (hpatch : (S∩relativeZeroNeighborhood S F).Nonempty) : ∀ a∈S,F a=0 := by
  let Z := relativeZeroNeighborhood S F
  have hZ : IsOpen Z := isOpen_interior
  have hsub : S⊆Z := by
    intro a ha
    by_contra hn
    have hcover : S⊆Z∪(S∩Z)ᶜ := by
      intro b hb
      by_cases hz : b∈Z
      · exact Or.inl hz
      · exact Or.inr (fun hd => hz hd.2)
    obtain ⟨b,hbS,hbZ,hbn⟩ := hS Z (S∩Z)ᶜ hZ hD.isOpen_compl hcover hpatch
      ⟨a,ha,fun hd => hn hd.2⟩
    exact hbn ⟨hbS,hbZ⟩
  exact fun a ha => relativeZeroNeighborhood_zero ha (hsub ha)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_zero_germs_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    IsClosed (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) (fun a => ⟪v,N (representative a)⟫)) := by
  let S := frontier (openRepresentative E)
  let F : Torus → ℝ := fun a => ⟪v,N (representative a)⟫
  let Z := relativeZeroNeighborhood S F
  let D := S∩Z
  have hD : D⊆S := inter_subset_left
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal hD isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hm
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε ≤ r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  have hw : PlaneSmooth w := normalTranslationNumerator_contDiff n hg v σ
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := by
    change w y=cmcWeight (gradient g y)*⟪v,N (representative (φ y))⟫
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _,(hb y hy).1]
    exact normalTranslationNumerator_weight hn g v σ y
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hD
    (hcover.mono fun z hz => hz.mp) (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc ε hε
  have hyb : y∈Metric.ball (0 : Plane) ε := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 ε) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hyO : y∈φ ⁻¹' Z∩Metric.ball 0 ε := ⟨hyD.2,hyb⟩
  have hzeroO : φ ⁻¹' Z∩Metric.ball 0 ε⊆{z | w z=0} := by
    intro z hz
    change w z=0
    rw [hws z hz.2,relativeZeroNeighborhood_zero (hb z hz.2).2 hz.1,mul_zero]
  have hpatch : (Metric.ball (0 : Plane) ε∩interior {z | w z=0}).Nonempty :=
    ⟨y,hyb,(hO.subset_interior_iff.mpr hzeroO) hyO⟩
  have hvan := (normalTranslationNumerator_linear n hg v σ hlin |>.mono
    (Metric.ball_subset_ball hεr)).unique_continuation hg hw Metric.isOpen_ball
      (convex_ball (0 : Plane) ε).isPreconnected hpatch
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_zero_germ (hcover.mono fun z hz => hz.mp)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
  have hz := hvan y hy
  rw [hws y hy] at hz
  exact (mul_eq_zero.mp hz).resolve_left (cmcWeight_pos _).ne'

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

theorem isMinimizerAt_normal_coordinate_seam_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) {a : Torus}
    (ha : a∈frontier (openRepresentative E)) (hz : coordinateSine i (representative a)=0) :
    N (representative a) i=0 := by
  have hh := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
    (representative a) (by rwa [quotientMap_representative]))
  simp only [coverCoordinateReflection_apply,ite_true] at hh
  have he : N (coverCoordinateReflection i (representative a))=N (representative a) := by
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_fixed_of_sine_zero i hz]
  rw [he] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma HasDerivAt.eq_zero_of_right_zero {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0)
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ),f t=0) : d=0 := by
  have hp := deriv_nonneg_of_right_min hd (hf.mono fun t ht => by rw [h0,ht])
  have hn := deriv_nonneg_of_right_min hd.neg (hf.mono fun t ht => by
    simp only [Pi.neg_apply,h0,ht,neg_zero,le_refl])
  linarith

lemma HasDerivAt.neg_right_of_neg {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0) (hd0 : d<0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),f t<0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  filter_upwards [ht.eventually (eventually_lt_nhds hd0),self_mem_nhdsWithin] with t hs ht
  rw [slope_def_field,h0,sub_zero,sub_zero] at hs
  simpa only [zero_mul] using (div_lt_iff₀ ht).mp hs

lemma plane_hasDerivAt_line {F : Plane → ℝ} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (v : Plane) :
    HasDerivAt (fun t : ℝ => F (y+t • v)) (fderiv ℝ F y v) 0 := by
  have hh : HasFDerivAt F (fderiv ℝ F y) (y+id (0 : ℝ) • v) := by
    simpa only [id_eq,zero_smul,add_zero] using hF.hasFDerivAt
  simpa only [Function.comp_def,id_eq,one_smul] using
    hh.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add y)

theorem not_differentiable_nodal_splice
    {u F : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R k : ℝ} (hR : 0<R) (hk : k≠0)
    (hy : ‖y-c‖=R) (huy : u y=0)
    (hhopf : 0<fderiv ℝ u y (c-y))
    (hin : ∀ x,‖x-c‖<R → F x=k*u x)
    (hout : ∀ᶠ x in 𝓝 y,u x≤0 → F x=0) :
    ¬DifferentiableAt ℝ F y := by
  intro hF
  let v := c-y
  have hn (t : ℝ) : ‖y+t • v-c‖=|1-t| * R := by
    rw [show y+t • v-c=(1-t) • (y-c) by dsimp [v]; module,
      norm_smul,Real.norm_eq_abs,hy]
  have huin := plane_hasDerivAt_line (hu.differentiable (by simp) y) v
  have hFin := plane_hasDerivAt_line hF v
  have hFy : F y=0 := (hout.self_of_nhds) huy.le
  have hi : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • v)-k*u (y+t • v)=0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    have ht0 : 0<t := ht
    rw [hin,sub_self]
    rw [hn,abs_of_pos (sub_pos.mpr ht1)]
    nlinarith
  have hid := HasDerivAt.eq_zero_of_right_zero (hFin.sub (huin.const_mul k)) (by
    simp only [Pi.sub_apply,zero_smul,add_zero,hFy,huy,mul_zero,sub_self]) hi
  have huout : HasDerivAt (fun t : ℝ => u (y+t • (-v))) (-fderiv ℝ u y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line (hu.differentiable (by simp) y) (-v)
  have hFout : HasDerivAt (fun t : ℝ => F (y+t • (-v))) (-fderiv ℝ F y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line hF (-v)
  have ho := HasDerivAt.neg_right_of_neg huout (by simp [huy]) (neg_neg_of_pos hhopf)
  have ht : Tendsto (fun t : ℝ => y+t • (-v)) (𝓝 0) (𝓝 y) := by
    convert (show Continuous (fun t : ℝ => y+t • (-v)) from
      continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hfo : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • (-v))=0 := by
    filter_upwards [ho,(ht.eventually hout).filter_mono nhdsWithin_le_nhds] with t ht hf
    exact hf ht.le
  have hod := HasDerivAt.eq_zero_of_right_zero hFout (by simp [hFy]) hfo
  have hm : k*fderiv ℝ u y v=0 := by linarith
  exact (mul_ne_zero hk (ne_of_gt hhopf)) hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.no_nodal_splice_frontier
    {g u F : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {D : Set Plane} (hD : IsOpen D)
    {a : Plane} {ε k : ℝ} (hε : 0<ε) (hk : k≠0)
    (hp : ∀ x∈Metric.ball a ε,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball a ε))
    (hpos : ∀ x∈D∩Metric.ball a ε,0<u x)
    (hz : ∀ x∈frontier D∩Metric.ball a ε,u x=0)
    (hin : ∀ x∈D∩Metric.ball a ε,F x=k*u x)
    (hout : ∀ x∈Metric.ball a ε,u x≤0 → F x=0)
    (hF : DifferentiableOn ℝ F (Metric.ball a ε)) : a∉frontier D := by
  intro ha
  obtain ⟨c,y,R,hR,hball,hy,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
  have hb : Metric.ball c R⊆Metric.ball a ε := Metric.ball_subset_closedBall.trans hsub
  have hyb : y∈Metric.ball a ε := hsub (by
    simpa only [Metric.mem_closedBall,dist_eq_norm,hy] using (le_refl R))
  have huy := hz y ⟨hyD,hyb⟩
  have hh := (hw.mono hb).hopf hg hu hR (fun x hx => hp x (hsub hx))
    (fun x hx => hpos x ⟨hball hx,hb hx⟩) hy huy
  apply not_differentiable_nodal_splice hu hR hk hy huy hh ?_ ?_
    (hF.differentiableAt (Metric.isOpen_ball.mem_nhds hyb))
  · intro x hx
    have hx' : x∈Metric.ball c R := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    exact hin x ⟨hball hx',hb hx'⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyb] with x hx
    exact hout x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_nodal_weak_sign {X : Type*} [TopologicalSpace X]
    (S : Set X) (r : X → X) (f s : X → ℝ)
    (hc : IsPreconnected {a | a∈S ∧ 0<f a}) (hs : Continuous s)
    (hr : ∀ a∈S,r a∈S) (hfo : ∀ a∈S,f (r a)= -f a)
    (hso : ∀ a,s (r a)= -s a) (hz : ∀ a∈S,s a=0 → f a=0) :
    (∀ a∈S,s a<0 → 0≤f a) ∨ (∀ a∈S,s a<0 → f a≤0) := by
  by_cases hpos : ∃ a∈S,s a<0 ∧ 0<f a
  · obtain ⟨a,ha,hsa,hfa⟩ := hpos
    left
    intro b hb hsb
    by_contra hn
    have hfb : f b<0 := lt_of_not_ge hn
    have hrb : 0<f (r b) := by rw [hfo b hb]; linarith
    have hsrb : 0 < s (r b) := by rw [hso]; linarith
    obtain ⟨c,hcS,hcs⟩ := hc.intermediate_value ⟨ha,hfa⟩ ⟨hr b hb,hrb⟩ hs.continuousOn
      (show (0 : ℝ)∈Icc (s a) (s (r b)) from ⟨hsa.le,hsrb.le⟩)
    have hcf := hz c hcS.1 hcs
    exact (ne_of_gt hcS.2) hcf
  · right
    intro a ha hsa
    by_contra hn
    exact hpos ⟨a,ha,hsa,lt_of_not_ge hn⟩

lemma descent_coordinateSine_reflection (i : Fin 3) (a : Torus) :
    coordinateSine i (representative (coordinateReflection i a))= -coordinateSine i (representative a) := by
  rw [← quotientMap_representative a,← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [quotientMap_representative]

lemma positiveNormal_preconnected {E : Set Torus} {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (i : Fin 3)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    IsPreconnected {a | a∈frontier (openRepresentative E) ∧ 0<N (representative a) i} := by
  let f := directionalNormalScalar N hN hp (EuclideanSpace.single i 1)
  let S := frontier (openRepresentative E)
  let g : positiveBoundaryLocus f S → Torus := fun a => a.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  have he : Set.range g={a | a∈S ∧ 0<N (representative a) i} := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      refine ⟨b.val.property,?_⟩
      have hh := b.property
      simpa only [f,positiveBoundaryLocus,mem_ofPred_eq,directionalNormalScalar_apply,
        EuclideanSpace.inner_single_left,map_one,one_mul,g] using hh
    · rintro ⟨ha,hp'⟩
      refine ⟨⟨⟨a,ha⟩,?_⟩,rfl⟩
      simpa only [f,positiveBoundaryLocus,mem_ofPred_eq,directionalNormalScalar_apply,
        EuclideanSpace.inner_single_left,map_one,one_mul,g] using hp'
  rw [← he]
  exact isPreconnected_range hg

theorem isMinimizerAt_normal_coordinate_weak_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0≤N (representative a) i) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i≤0) := by
  have hr : ∀ a∈frontier (openRepresentative E),coordinateReflection i a∈frontier (openRepresentative E) := by
    intro a ha
    change a∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rwa [frontier_reflection_invariant hE i hs]
  have hfo : ∀ a∈frontier (openRepresentative E),
      N (representative (coordinateReflection i a)) i= -N (representative a) i := by
    intro a ha
    have hh := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
      (representative a) (by rwa [quotientMap_representative]))
    simp only [coverCoordinateReflection_apply,ite_true] at hh
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative] at hh
    linarith
  have hz : ∀ a∈frontier (openRepresentative E),coordinateSine i (representative a)=0 →
      N (representative a) i=0 := fun a ha hz =>
        isMinimizerAt_normal_coordinate_seam_zero hV hE hmE hμ hN hp hae i hs ha hz
  obtain h|h := reflection_nodal_weak_sign (frontier (openRepresentative E)) (coordinateReflection i)
    (fun a => N (representative a) i) (fun a => coordinateSine i (representative a))
    (positiveNormal_preconnected hN hp i)
    (continuous_periodic_descent (coordinateSine_contDiff i).continuous (coordinateSine_periodic i))
    hr hfo (descent_coordinateSine_reflection i) hz
  · left; intro a ha; exact h a ha.1 (by simpa only [coordinateHalf_zero,sublevelRegion,mem_ofPred_eq] using ha.2)
  · right; intro a ha; exact h a ha.1 (by simpa only [coordinateHalf_zero,sublevelRegion,mem_ofPred_eq] using ha.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.nonneg_zero {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set Plane} (hU : IsOpen U) (hc : IsPreconnected U)
    (hp : ∀ x∈U,‖gradient g x‖≤1) (hw : LinearCMCEquation u (gradient g) (fun _ => 0) U)
    (hn : ∀ x∈U,0≤u x) {a : Plane} (ha : a∈U) (hz : u a=0) :
    ∀ x∈U,u x=0 := by
  let D := {x : Plane | 0<u x}
  have hD : IsOpen D := isOpen_lt continuous_const hu.continuous
  have hfr : Disjoint U (frontier D) := by
    rw [disjoint_left]
    intro z hzU hzD
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hzU
    apply (hw.mono hεU).no_nodal_splice_frontier hg hu hD hε (by norm_num : (1 : ℝ)≠0)
      (fun x hx => hp x (hεU hx)) (fun x hx => hx.1) ?_ ?_ ?_
      (hu.differentiable (by simp)).differentiableOn hzD
    · intro x hx
      have h₁ : 0≤u x := hn x (hεU hx.2)
      have h₂ : ¬0<u x := by
        have hh : x∉D := by
          have ht := hx.1.2
          simpa only [hD.interior_eq] using ht
        exact hh
      exact le_antisymm (le_of_not_gt h₂) h₁
    · intro x _; simp only [one_mul]
    · intro x hx hux
      exact le_antisymm hux (hn x (hεU hx))
  intro x hx
  by_contra hnz
  have hpos : 0<u x := lt_of_le_of_ne (hn x hx) (Ne.symm hnz)
  obtain ⟨z,hzU,hzD⟩ := preconnected_crosses_frontier hc hD ⟨x,hx,hpos⟩ ⟨a,ha,by
    change ¬0<u a
    rw [hz]
    exact lt_irrefl _⟩
  exact disjoint_left.mp hfr hzU hzD

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_MinimizerAxialCenter
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

theorem isMinimizerAt_normal_one_sign_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover)
    {U : Set Torus} (hU : IsOpen U)
    (hpos : ∀ a∈frontier (openRepresentative E)∩U,0≤⟪v,N (representative a)⟫)
    {a : Torus} (ha : a∈frontier (openRepresentative E)∩U)
    (hz : ⟪v,N (representative a)⟫=0) :
    ∀ b∈frontier (openRepresentative E),⟪v,N (representative b)⟫=0 := by
  let S := frontier (openRepresentative E)
  let F : Torus → ℝ := fun b => ⟪v,N (representative b)⟫
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rw [hxa]; exact ha.1
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry n) 0+g 0 • n=0
    simp only [map_zero,hg0,zero_smul,add_zero]
  have hφ0 : φ 0=a := by simp only [φ,hG0,add_zero,hxa]
  have hmU : ∀ᶠ y in 𝓝 (0 : Plane),
      (N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S) ∧ φ y∈U :=
    hm.and (hφ.continuousAt.eventually (by rw [hφ0]; exact hU.mem_nhds ha.2))
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hmU
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε ≤ r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := normalTranslationNumerator_contDiff n hg v σ
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := by
    change w y=cmcWeight (gradient g y)*⟪v,N (representative (φ y))⟫
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _,(hb y hy).1.1]
    exact normalTranslationNumerator_weight hn g v σ y
  have hzero : ∀ y∈Metric.ball (0 : Plane) ε,w y=0 := by
    apply (normalTranslationNumerator_linear n hg v σ hlin |>.mono
      (Metric.ball_subset_ball hεr)).nonneg_zero hg hw Metric.isOpen_ball
      (convex_ball (0 : Plane) ε).isPreconnected
      (fun y hy => hgrad y (Metric.ball_subset_ball hεr hy))
    · intro y hy
      rw [hws y hy]
      exact mul_nonneg (cmcWeight_pos _).le (hpos _ ⟨(hb y hy).1.2,(hb y hy).2⟩)
    · exact Metric.mem_ball_self hε
    · rw [hws 0 (Metric.mem_ball_self hε),hφ0]
      change cmcWeight _*⟪v,N (representative a)⟫=0
      rw [hz,mul_zero]
  have hag : a∈relativeZeroNeighborhood S F := by
    rw [← hxa]
    apply quotient_graph_zero_germ (hcover.mono fun z hz => hz.mp)
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
    have hh := hzero y hy
    rw [hws y hy] at hh
    exact (mul_eq_zero.mp hh).resolve_left (cmcWeight_pos _).ne'
  exact preconnected_zero_of_closed_germ hS
    (isMinimizerAt_normal_zero_germs_closed hV hE hmin hμ hN hp hae v) ⟨a,ha.1,hag⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_coordinate_strict_or_zero_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    (∀ a∈frontier (openRepresentative E),N (representative a) i=0) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0) := by
  by_cases hall : ∀ a∈frontier (openRepresentative E),N (representative a) i=0
  · exact Or.inl hall
  right
  obtain hpos|hneg := isMinimizerAt_normal_coordinate_weak_sign hV hE hmE hμ hN hp hae i hs
  · left
    intro a ha
    apply lt_of_le_of_ne (hpos a ha)
    intro hza
    apply hall
    have hh := isMinimizerAt_normal_one_sign_zero hV hE hmE hc hμ hN hp hae
      (EuclideanSpace.single i 1) (coordinateHalf_open i) (fun b hb => by
        simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hpos b hb) ha
      (by simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hza.symm)
    simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hh
  · right
    intro a ha
    apply lt_of_le_of_ne (hneg a ha)
    intro hza
    apply hall
    have hh := isMinimizerAt_normal_one_sign_zero hV hE hmE hc hμ hN hp hae
      (-EuclideanSpace.single i 1) (coordinateHalf_open i) (fun b hb => by
        simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_nonneg] using hneg b hb) ha
      (by simp only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,hza,neg_zero])
    simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_eq_zero] using hh

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero_oai := @OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero_oai
