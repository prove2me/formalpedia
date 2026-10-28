-- Prove2me | solution 1 for OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:08:46.098383+00:00
-- url     : https://prove2.me/submissions/c309440f-c9c4-4507-9edb-73f2bdc63029

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae

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

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

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
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
attribute [-instance] _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.plane_hausdorff_two_haar
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

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
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

lemma coordinateSectionPoint_contDiff (c : Cover) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateSectionPoint c t) :=
  contDiff_const.add coordinatePlaneLift.contDiff

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

lemma measurableSet_transverseSquare : MeasurableSet transverseSquare := by
  change MeasurableSet {y : Plane | ∀ j,y j∈Ico (0 : ℝ) 1}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j =>
    measurableSet_Ico.preimage (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).measurable)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

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

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlanarRadialArea
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

lemma measurableSet_planarRadialRegion {r : ℝ → ℝ} (hr : Measurable r) :
    MeasurableSet (planarRadialRegion r) :=
  measurableSet_lt measurable_norm (hr.comp (Complex.measurable_arg.div_const _))

lemma mem_planarRadialRegion_polar {r : ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p∈Complex.polarCoord.target) :
    Complex.polarCoord.symm p∈planarRadialRegion r ↔ p.1 < r (p.2/(2*Real.pi)) := by
  have he := congrArg Prod.snd (Complex.polarCoord.right_inv hp)
  rw [Complex.polarCoord_apply] at he
  change (Complex.polarCoord.symm p).arg=p.2 at he
  change ‖Complex.polarCoord.symm p‖ < r _ ↔ _
  rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1,he]

lemma lintegral_radial_coordinate {R : ℝ} (hR : 0≤R) :
    (∫⁻ x in Ioi (0 : ℝ),if x<R then ENNReal.ofReal x else 0)=ENNReal.ofReal (R^2/2) := by
  have he : (fun x : ℝ => if x<R then ENNReal.ofReal x else 0)=
      (Iio R).indicator ENNReal.ofReal := by rfl
  rw [he,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  rw [inter_comm,Ioi_inter_Iio,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hi : IntegrableOn (fun x : ℝ => x) (Ioc 0 R) :=
    (continuous_id.intervalIntegrable 0 R).1.mono_set (by rfl)
  have hn : 0≤ᵐ[volume.restrict (Ioc 0 R)] (fun x : ℝ => x) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← intervalIntegral.integral_of_le hR,integral_id]
  simp

theorem volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0 < r t) :
    volume (planarRadialRegion r)=
      ENNReal.ofReal (Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2)) := by
  let f : ℂ → ℝ≥0∞ := (planarRadialRegion r).indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator (measurableSet_planarRadialRegion hr.measurable)
  have hvol : (∫⁻ z,f z)=volume (planarRadialRegion r) := by
    simp [f,lintegral_indicator,measurableSet_planarRadialRegion hr.measurable]
  rw [← hvol,← Complex.lintegral_comp_polarCoord_symm]
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 < r (p.2/(2*Real.pi)) then ENNReal.ofReal p.1 else 0
  have hgm : Measurable g := by
    exact Measurable.ite (measurableSet_lt measurable_fst
      (hr.measurable.comp (measurable_snd.div_const _)))
      measurable_fst.ennreal_ofReal measurable_const
  have hg : (∫⁻ p in polarCoord.target,ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p))=
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,g p := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp'
    have hmem := mem_planarRadialRegion_polar (r := r) hp'
    by_cases hh : p.1 < r (p.2/(2*Real.pi))
    · simp only [f,g,indicator_of_mem (hmem.mpr hh),ite_eq_left hh,smul_eq_mul,mul_one]
    · simp only [f,g,indicator_of_notMem (not_imp_not.mpr hmem.mp hh),ite_eq_right hh,smul_eq_mul,mul_zero]
  rw [hg,Measure.volume_eq_prod,setLIntegral_prod _ hgm.aemeasurable]
  rw [lintegral_lintegral_swap hgm.aemeasurable]
  have hb : (∫⁻ t in Ioo (-Real.pi) Real.pi,∫⁻ x in Ioi (0 : ℝ),g (x,t))=
      ∫⁻ t in Ioo (-Real.pi) Real.pi,ENNReal.ofReal ((r (t/(2*Real.pi)))^2/2) := by
    apply lintegral_congr
    intro t
    exact lintegral_radial_coordinate (R := r (t/(2*Real.pi))) (hpos _).le
  rw [hb,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hrc : Continuous (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) :=
    ((hr.comp (continuous_id.div_const _)).pow 2).div_const _
  have hpi : -Real.pi≤Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) (Ioc (-Real.pi) Real.pi) := by
    exact (hrc.intervalIntegrable (-Real.pi) Real.pi).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity)),
    ← intervalIntegral.integral_of_le hpi]
  congr 1
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div (fun t => (r t)^2) (by positivity : 2*Real.pi≠0)]
  have hlo : -Real.pi/(2*Real.pi)= -(1/2 : ℝ) := by field_simp
  have hhi : Real.pi/(2*Real.pi)=(1/2 : ℝ) := by field_simp
  rw [hlo,hhi]
  have hper : Function.Periodic (fun t => (r t)^2) 1 := fun t => congrArg (fun a : ℝ => a^2) (hp t)
  have hs := hper.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  norm_num only [neg_add_cancel_left,zero_add] at hs
  have hs' : (∫ t in (-(1/2) : ℝ)..(1/2),(r t)^2)=∫ t in (0 : ℝ)..1,(r t)^2 := by
    exact hs
  rw [hs']
  simp only [smul_eq_mul]
  ring

lemma real_volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0 < r t) :
    volume.real (planarRadialRegion r)=Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2) := by
  rw [Measure.real,volume_planarRadialRegion hr hp hpos,ENNReal.toReal_ofReal]
  exact mul_nonneg Real.pi_pos.le
    (intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg (r t)))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_RadialSectionArea
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

lemma norm_smul_unitAngle_arg (z : ℂ) : ‖z‖ • unitAngle (z.arg/(2*Real.pi))=z := by
  rw [unitAngle]
  have he : 2*Real.pi*(z.arg/(2*Real.pi))=z.arg := by field_simp
  rw [he,Complex.real_smul]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma radius_le_squareScale_of_gauge {z : ℂ} (hz : complexSquareGauge z≤1/2) :
    ‖z‖≤unitSquareScale (z.arg/(2*Real.pi)) := by
  let a := z.arg/(2*Real.pi)
  have hh : ‖z‖*complexSquareGauge (unitAngle a)≤1/2 := by
    rw [← complexSquareGauge_smul (norm_nonneg z),norm_smul_unitAngle_arg]
    exact hz
  rw [unitSquareScale,le_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))]
  nlinarith

lemma planarRadialRegion_eq_actual_section {E : Set Torus} {c : Cover} {t : ℝ} {r : ℝ → ℝ}
    (hr0 : ∀ a,0 < r a) (hrb : ∀ a,r a<unitSquareScale a)
    (hphase : ∀ a u,0≤u → u≤unitSquareScale a →
      (quotientMap (coordinateSectionPoint c t (u • unitAngle a))∈E ↔ u < r a)) :
    planarRadialRegion r=centeredPlaneSection E c t := by
  ext z
  let a := z.arg/(2*Real.pi)
  have hg : 0 < complexSquareGauge (unitAngle a) := complexSquareGauge_pos (unitAngle_ne_zero a)
  have hgs : unitSquareScale a*complexSquareGauge (unitAngle a)=1/2 := by
    dsimp [unitSquareScale]
    field_simp [hg.ne']
  change ‖z‖ < r a ↔ complexSquareGauge z<1/2 ∧ quotientMap (coordinateSectionPoint c t z)∈E
  constructor
  · intro hz
    have hb : ‖z‖≤unitSquareScale a := (hz.trans (hrb a)).le
    refine ⟨?_,?_⟩
    · rw [← norm_smul_unitAngle_arg z,complexSquareGauge_smul (norm_nonneg z)]
      exact (mul_lt_mul_of_pos_right (hz.trans (hrb a)) hg).trans_eq hgs
    · have he := (hphase a ‖z‖ (norm_nonneg z) hb).mpr hz
      rwa [norm_smul_unitAngle_arg] at he
  · rintro ⟨hz,hE⟩
    rcases (norm_nonneg z).eq_or_lt with hzero | hpos
    · rw [← hzero]
      exact hr0 a
    · apply (hphase a ‖z‖ hpos.le (radius_le_squareScale_of_gauge hz.le)).mp
      rwa [norm_smul_unitAngle_arg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_integral_unit_translate {f : ℝ → ℝ} (hp : Function.Periodic f 1) (a c : ℝ) :
    (∫ x in Ioo a (a+1),f (x+c))=∫ x in Ico (0 : ℝ) 1,f x := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : a≤a+1),
    intervalIntegral.integral_comp_add_right,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  convert hp.intervalIntegral_add_eq (a+c) 0 using 1 <;> congr 1 <;> ring

lemma bounded_integrable_rectangle {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) (a b c d : ℝ) :
    IntegrableOn f (Ioo a b ×ˢ Ioo c d) := by
  apply IntegrableOn.of_bound (by
    rw [Measure.volume_eq_prod]
    simp only [Measure.prod_prod,Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma bounded_integrable_unit_square {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) : IntegrableOn f (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (by rw [Measure.volume_eq_prod]; simp) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma periodic_plane_integral_translate {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M)
    (hx : ∀ y,Function.Periodic (fun x => f (x,y)) 1)
    (hy : ∀ x,Function.Periodic (fun y => f (x,y)) 1) (a b c d : ℝ) :
    (∫ z in Ioo a (a+1) ×ˢ Ioo b (b+1),f (z.1+c,z.2+d))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,f z := by
  have hmeas : Measurable (fun z : ℝ × ℝ => f (z.1+c,z.2+d)) :=
    hf.comp ((measurable_fst.add_const c).prodMk (measurable_snd.add_const d))
  have hi := bounded_integrable_rectangle hmeas (fun z => hb (z.1+c,z.2+d)) a (a+1) b (b+1)
  have hj := bounded_integrable_unit_square hf hb
  rw [Measure.volume_eq_prod] at hi hj ⊢
  rw [setIntegral_prod _ hi,setIntegral_prod _ hj]
  simp_rw [periodic_integral_unit_translate (hy _) b d]
  apply periodic_integral_unit_translate (f := fun x => ∫ y in Ico (0 : ℝ) 1,f (x,y))
  intro x
  apply setIntegral_congr_fun measurableSet_Ico
  intro y _
  exact hx y x

lemma axialSplit_zero_symm (t : ℝ) (y : Plane) :
    (axialSplit 0).symm (t,y)=UpperComparison.tubeSplit.symm (t,y) := by
  ext i
  simp [axialSplit,coverCoordinatePermute,LinearIsometryEquiv.piLpCongrLeft_apply]

lemma coordinateSectionPoint_coordinates (c : Cover) (t : ℝ) (z : ℂ) :
    coordinateSectionPoint c t z=(axialSplit 0).symm
      (t,planeProductCoordinates.symm (z.re+c 1,z.im+c 2)) := by
  rw [axialSplit_zero_symm]
  ext i
  fin_cases i <;> simp [planeProductCoordinates_symm_apply] <;> ring

lemma centered_complex_integral_periodic {f : Cover → ℝ} (hf : Measurable f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) {M : ℝ} (hb : ∀ x,‖f x‖≤M)
    (c : Cover) (t : ℝ) :
    (∫ z in {z : ℂ | complexSquareGauge z<1/2},f (coordinateSectionPoint c t z))=
      ∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)) := by
  let g : ℝ × ℝ → ℝ := fun z => f ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
  have hg : Measurable g := hf.comp ((axialSplit 0).symm.measurable.comp
    (measurable_const.prodMk planeProductCoordinates.symm.continuous.measurable))
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))=
      {z : ℂ | complexSquareGauge z<1/2} := by
    ext z
    simp [complexSquareGauge,abs_lt,max_lt_iff,Complex.measurableEquivRealProd]
  have hc := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ × ℝ => g (z.1+c 1,z.2+c 2))
    (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))
  rw [hpre] at hc
  have hfun : (fun z : ℂ => g ((Complex.measurableEquivRealProd z).1+c 1,
      (Complex.measurableEquivRealProd z).2+c 2))=(fun z => f (coordinateSectionPoint c t z)) := by
    funext z
    dsimp [g]
    rw [coordinateSectionPoint_coordinates]
  rw [hfun] at hc
  rw [hc]
  have hpp : planeProductCoordinates ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)=transverseSquare := by
    ext y
    simp only [mem_preimage,planeProductCoordinates_apply,mem_prod,mem_Ico,transverseSquare,mem_ofPred_eq]
    constructor
    · intro h j
      fin_cases j <;> tauto
    · intro h
      exact ⟨h 0,h 1⟩
  have he := planeProductCoordinates_measurePreserving.setIntegral_preimage_emb
    planeProductCoordinates.toHomeomorph.measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)
  rw [hpp] at he
  have he' : (∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,g z := by simpa only [g,ContinuousLinearEquiv.symm_apply_apply] using he
  rw [he']
  have hperiod (j : Fin 2) (z : ℝ × ℝ) :
      g (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2)=g z := by
    have hh := hp (Pi.single j.succ (1 : ℤ)) ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
    have hv : (axialSplit 0).symm (t,planeProductCoordinates.symm
        (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2))=
        (axialSplit 0).symm (t,planeProductCoordinates.symm z)+latticeVector (Pi.single j.succ (1 : ℤ)) := by
      rw [axialSplit_zero_symm,axialSplit_zero_symm]
      ext i
      fin_cases i <;> fin_cases j <;> simp [planeProductCoordinates_symm_apply,latticeVector,Pi.single_apply]
    dsimp only [g]
    rw [hv]
    exact hh
  have hx : ∀ y,Function.Periodic (fun x => g (x,y)) 1 := by
    intro y x
    simpa using hperiod 0 (x,y)
  have hy : ∀ x,Function.Periodic (fun y => g (x,y)) 1 := by
    intro x y
    simpa using hperiod 1 (x,y)
  convert periodic_plane_integral_translate hg (fun z => hb _) hx hy (-(1/2)) (-(1/2)) (c 1) (c 2) using 1; norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma centeredPlaneSection_integral {E : Set Torus} (hE : MeasurableSet E)
    {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x)
    (c : Cover) (t : ℝ) :
    (∫ z in centeredPlaneSection E c t,g (coordinateSectionPoint c t z))=
      axialSectionIntegral E 0 g t := by
  let f : Cover → ℝ := fun x => characteristic E (quotientMap x)*g x
  have hf : Measurable f := ((measurable_characteristic hE).comp measurable_quotientMap).mul hg.measurable
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp [f,quotientMap_add,quotientMap_latticeVector,hp]
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  have hb : ∀ x,‖f x‖≤M := by
    intro x
    change ‖characteristic E (quotientMap x)*g x‖≤M
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM x)
  have he := centered_complex_integral_periodic hf hfp hb c t
  have hfun : (fun z => f (coordinateSectionPoint c t z))=
      ((fun z => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E).indicator
        (fun z => g (coordinateSectionPoint c t z)) := by
    funext z
    by_cases hz : quotientMap (coordinateSectionPoint c t z)∈E <;> simp [f,characteristic,hz]
  have hms : MeasurableSet ((fun z : ℂ => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E) :=
    hE.preimage (measurable_quotientMap.comp (coordinateSectionPoint_contDiff c t).continuous.measurable)
  rw [hfun] at he
  rw [setIntegral_indicator hms] at he
  exact he

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

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_RevolutionTangents
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

lemma axisRadialField_contDiff (c : Cover) {α β g : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (axisRadialField c α β g) := by
  have hx (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover => x i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  exact (((hα.comp (hx 0)).smul contDiff_const).add
    (((hβ.comp (hx 0)).mul (hg.comp ((hx 1).sub contDiff_const))).smul contDiff_const)).add
    (((hβ.comp (hx 0)).mul (hg.comp ((hx 2).sub contDiff_const))).smul contDiff_const)

lemma axisRadialField_periodic (c : Cover) {α β g : ℝ → ℝ}
    (hα : Function.Periodic α 1) (hβ : Function.Periodic β 1)
    (hg : Function.Periodic g 1) :
    ∀ m x,axisRadialField c α β g (x+latticeVector m)=axisRadialField c α β g x := by
  intro m x
  have ha : α (x 0+(m 0 : ℝ))=α (x 0) := by simpa using hα.int_mul (m 0) (x 0)
  have hb : β (x 0+(m 0 : ℝ))=β (x 0) := by simpa using hβ.int_mul (m 0) (x 0)
  have he (i : Fin 3) : g (x i+(m i : ℝ)-c i)=g (x i-c i) := by
    convert hg.int_mul (m i) (x i-c i) using 1; congr 1; ring
  simp only [axisRadialField,PiLp.add_apply,latticeVector,ha,hb,he]

lemma divergence_axisRadialField (c x : Cover) {α β g : ℝ → ℝ}
    (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) (hg : Differentiable ℝ g) :
    divergence (axisRadialField c α β g) x=
      deriv α (x 0)+β (x 0)*(deriv g (x 1-c 1)+deriv g (x 2-c 2)) := by
  have hd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (i : Fin 3) (d : ℝ) :
      HasFDerivAt (fun y : Cover => f (y i-d))
        ((deriv f (x i-d)) • (EuclideanSpace.proj i : Cover →L[ℝ] ℝ)) x := by
    convert! (hf (x i-d)).hasDerivAt.hasFDerivAt.comp x
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt).sub_const d) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp [mul_comm]
  have ha := hd α hα 0 0
  have hb := hd β hβ 0 0
  simp only [sub_zero] at ha hb
  have h₁ := hb.mul (hd g hg 1 (c 1))
  have h₂ := hb.mul (hd g hg 2 (c 2))
  have htot := ((ha.smul_const (EuclideanSpace.single 0 1 : Cover)).add
    (h₁.smul_const (EuclideanSpace.single 1 1 : Cover))).add
      (h₂.smul_const (EuclideanSpace.single 2 1 : Cover))
  change HasFDerivAt (axisRadialField c α β g) _ x at htot
  unfold divergence
  rw [htot.fderiv]
  simp [Fin.sum_univ_succ,EuclideanSpace.proj]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.revolution_section {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) (t : ℝ) :
    centeredPlaneSection (openRepresentative E) c t={z : ℂ | ‖z‖ < r (t,0)} := by
  have he := planarRadialRegion_eq_actual_section
    (fun a => (hr.2.2.2.1 (t,a)).1) (fun a => (hr.2.2.2.1 (t,a)).2)
    (fun a u hu hub => hr.2.2.2.2.2.1 (t,a) u hu hub)
  rw [← he]
  ext z
  simp only [planarRadialRegion,mem_ofPred_eq,hangle]

lemma TrueRadialTube.revolution_section_volume {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) (t : ℝ) :
    volume.real (centeredPlaneSection (openRepresentative E) c t)=Real.pi*r (t,0)^2 := by
  have he := planarRadialRegion_eq_actual_section
    (fun a => (hr.2.2.2.1 (t,a)).1) (fun a => (hr.2.2.2.1 (t,a)).2)
    (fun a u hu hub => hr.2.2.2.2.2.1 (t,a) u hu hub)
  rw [← he,real_volume_planarRadialRegion
    (show Continuous (fun a => r (t,a)) from hr.1.continuous.comp (continuous_const.prodMk continuous_id)) (hr.2.2.1 t)
      (fun a => (hr.2.2.2.1 (t,a)).1)]
  simp only [hangle,intervalIntegral.integral_const,sub_zero,one_smul]

lemma TrueRadialTube.revolution_radius_bound {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (_hangle : ∀ t a,r (t,a)=r (t,0)) :
    ∃ R : ℝ,0≤R ∧ R<1/2 ∧ ∀ t,r (t,0)≤R := by
  obtain ⟨R,hR,hRb,hb⟩ := hr.uniform_square_gap
  refine ⟨R,hR,hRb,fun t => ?_⟩
  have h := hb (t,0)
  have hp := (hr.2.2.2.1 (t,0)).1
  exact (by simpa [unitAngle_zero,complexSquareGauge,abs_of_pos hp] using h : r (t,0)≤R ∧ 0≤R).1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_boundary_flux_le {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x)
    (hb : ∀ x,quotientMap x∈frontier (openRepresentative E) → ‖F x‖≤1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x)≤(perimeter E).toReal := by
  obtain ⟨C,hC0,hC⟩ := periodic_bounded hF.continuous hp
  rw [← normalMeasure_flux hμ hF hp (show 0<C+1 by linarith)
    (fun x => (hC x).trans (by linarith : C≤C+1))]
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm)
  calc
    _ ≤ ∫ _z : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae
        ((normalTest F hF.continuous).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      filter_upwards [hbd] with z hz
      calc
        _ ≤ ‖(z.2 : Cover)‖*‖F z.1‖ := real_inner_le_norm _ _
        _ ≤ 1 := by simpa only [z.2.property,one_mul] using hb z.1 hz
    _ = (perimeter E).toReal := by
      rw [integral_const,smul_eq_mul,mul_one,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.axisRadialField_boundary_bound {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) {α β g : ℝ → ℝ}
    (hα : Function.Periodic α 1) (hβ : Function.Periodic β 1)
    (hg : Function.Periodic g 1)
    (he : ∀ t a,g (r (t,0)*(unitAngle a).re)=r (t,0)*(unitAngle a).re ∧
      g (r (t,0)*(unitAngle a).im)=r (t,0)*(unitAngle a).im)
    (hb : ∀ t,α t^2+(β t*r (t,0))^2≤1) :
    ∀ x,quotientMap x∈frontier (openRepresentative E) →
      ‖axisRadialField c α β g x‖≤1 := by
  intro x hx
  rw [← hr.boundary_range] at hx
  obtain ⟨p,hpx⟩ := hx
  obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
  rw [hm,axisRadialField_periodic c hα hβ hg]
  have hn := congrArg (fun z : ℝ => z^2) (unitAngle_norm p.2)
  rw [Complex.sq_norm] at hn
  simp only [Complex.normSq_apply,one_pow] at hn
  have hsq : ‖axisRadialField c α β g
      (coordinateSectionPoint c p.1 (r p • unitAngle p.2))‖^2≤1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    simp only [axisRadialField_zero,axisRadialField_one,axisRadialField_two,
      coordinateSectionPoint_apply]
    simp only [reduceIte,Fin.isValue,show (1 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,add_sub_cancel_left]
    rw [show r p=r (p.1,0) from hangle p.1 p.2,(he p.1 p.2).1,(he p.1 p.2).2]
    have hid : (β p.1*(r (p.1,0)*(unitAngle p.2).re))^2+
        (β p.1*(r (p.1,0)*(unitAngle p.2).im))^2=
        (β p.1*r (p.1,0))^2*((unitAngle p.2).re*(unitAngle p.2).re+
          (unitAngle p.2).im*(unitAngle p.2).im) := by ring
    rw [hn,mul_one] at hid
    linarith only [hb p.1,hid]
  nlinarith only [hsq,norm_nonneg (axisRadialField c α β g
    (coordinateSectionPoint c p.1 (r p • unitAngle p.2)))]

theorem TrueRadialTube.axisRadialField_flux {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) {α β g : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpα : Function.Periodic α 1) (hpβ : Function.Periodic β 1)
    (hpg : Function.Periodic g 1)
    (he : ∀ t y,|y| < r (t,0) → deriv g y=1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' openRepresentative E,
      divergence (axisRadialField c α β g) x)=
      Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)^2*(deriv α t+2*β t)) := by
  have hF := axisRadialField_contDiff c hα hβ hg
  have hFp := axisRadialField_periodic c hpα hpβ hpg
  have hU := (isOpen_openRepresentative E).measurableSet
  rw [axial_weighted_section_fubini hU 0 (continuous_divergence hF) (divergence_periodic hFp)]
  have hh (t : ℝ) : axialSectionIntegral (openRepresentative E) 0
      (divergence (axisRadialField c α β g)) t=
      Real.pi*(r (t,0)^2*(deriv α t+2*β t)) := by
    rw [← centeredPlaneSection_integral hU (continuous_divergence hF) (divergence_periodic hFp) c]
    have hs : (∫ z in centeredPlaneSection (openRepresentative E) c t,
        divergence (axisRadialField c α β g) (coordinateSectionPoint c t z))=
        ∫ _z in centeredPlaneSection (openRepresentative E) c t,(deriv α t+2*β t) := by
      apply setIntegral_congr_fun (show MeasurableSet (centeredPlaneSection (openRepresentative E) c t) from by
        rw [hr.revolution_section hangle]
        exact (isOpen_lt continuous_norm continuous_const).measurableSet)
      intro z hz
      rw [hr.revolution_section hangle] at hz
      have hz' : ‖z‖ < r (t,0) := hz
      change divergence (axisRadialField c α β g) (coordinateSectionPoint c t z)=_
      rw [divergence_axisRadialField c _ (hα.differentiable (by simp))
        (hβ.differentiable (by simp)) (hg.differentiable (by simp))]
      simp only [coordinateSectionPoint_apply]
      simp only [reduceIte,Fin.isValue,show (1 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false,add_sub_cancel_left]
      rw [he t z.re ((Complex.abs_re_le_norm z).trans_lt hz'),
        he t z.im ((Complex.abs_im_le_norm z).trans_lt hz')]
      ring
    rw [hs,integral_const,smul_eq_mul]
    simp only [Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real_def,hr.revolution_section_volume hangle]
    ring
  simp_rw [hh]
  rw [integral_const_mul,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_DelaunayPeriodicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
namespace CubicTorus

theorem periodic_revolution_flux_integral {r p α β : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : Continuous p)
    (hpos : ∀ t,0 < r t) (hrp : Function.Periodic r 1)
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαp : Function.Periodic α 1)
    (heα : ∀ t,α t= -(p t)/Real.sqrt (1+p t^2))
    (heβ : ∀ t,β t=1/(r t*Real.sqrt (1+p t^2))) :
    (∫ t in (0 : ℝ)..1,r t^2*(deriv α t+2*β t))=
      2*(∫ t in (0 : ℝ)..1,r t*Real.sqrt (1+p t^2)) := by
  have hc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hda : Continuous (deriv α) := hα.continuous_deriv (by simp)
  let k := fun t => 2*r t*p t*α t+r t^2*deriv α t
  have hk : Continuous k := ((continuous_const.mul hc |>.mul hp).mul hα.continuous).add
    ((hc.pow 2).mul hda)
  have hd (t) : HasDerivAt (fun s => r s^2*α s) (k t) t := by
    convert! ((hr t).pow 2).mul ((hα.differentiable (by simp) t).hasDerivAt) using 1; simp [k]
  have hi : (∫ t in (0 : ℝ)..1,k t)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hk.intervalIntegrable 0 1)]
    have h1 : r 1=r 0 := by simpa only [zero_add] using hrp 0
    have h2 : α 1=α 0 := by simpa only [zero_add] using hαp 0
    rw [h1,h2,sub_self]
  have he (t) : r t^2*(deriv α t+2*β t)=k t+2*(r t*Real.sqrt (1+p t^2)) := by
    have hs0 : Real.sqrt (1+p t^2)≠0 := (Real.sqrt_pos.mpr (by positivity : 0<1+p t^2)).ne'
    have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
    have hr0 := (hpos t).ne'
    dsimp only [k]
    rw [heα t,heβ t]
    field_simp
    nlinarith only [hs2]
  have hA : Continuous (fun t => r t*Real.sqrt (1+p t^2)) :=
    hc.mul (continuous_const.add (hp.pow 2)).sqrt
  simp_rw [he]
  rw [intervalIntegral.integral_add (f := k) (g := fun t => 2*(r t*Real.sqrt (1+p t^2)))
      (hk.intervalIntegrable 0 1) ((hA.intervalIntegrable 0 1).const_mul 2),
    intervalIntegral.integral_const_mul,hi,zero_add]

lemma revolution_flux_coefficients_normal {r p : ℝ} (hr : 0 < r) :
    (-(p)/Real.sqrt (1+p^2))^2+(1/(r*Real.sqrt (1+p^2))*r)^2=1 := by
  have hs0 : Real.sqrt (1+p^2)≠0 := (Real.sqrt_pos.mpr (by positivity : 0<1+p^2)).ne'
  have hs2 := Real.sq_sqrt (show 0≤1+p^2 by positivity)
  have hr0 := hr.ne'
  field_simp
  nlinarith only [hs2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_deriv_real {r : ℝ → ℝ} (hr : Function.Periodic r 1) :
    Function.Periodic (deriv r) 1 := by
  intro t
  have he : (fun u => r (u+1))=r := funext hr
  rw [← deriv_comp_add_const,he]

theorem TrueRadialTube.revolution_area_le_perimeter_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    2*Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)*Real.sqrt (1+(deriv (fun u => r (u,0)) t)^2))≤
      (perimeter E).toReal := by
  let R := fun t => r (t,0)
  let p := deriv R
  let s := fun t => Real.sqrt (1+p t^2)
  let α := fun t => -(p t)/s t
  let β := fun t => 1/(R t*s t)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := hr.1.comp (contDiff_id.prodMk contDiff_const)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := (contDiff_infty_iff_deriv.mp hR).2
  have hRpos (t) : 0<R t := (hr.2.2.2.1 (t,0)).1
  have hspos (t) : 0 < s t := Real.sqrt_pos.mpr (by positivity)
  have hs : ContDiff ℝ (⊤ : ℕ∞) s :=
    (contDiff_const.add (hp.pow 2)).sqrt (fun t => (by positivity : 1+p t^2≠0))
  have hα : ContDiff ℝ (⊤ : ℕ∞) α := hp.neg.div hs (fun t => (hspos t).ne')
  have hβ : ContDiff ℝ (⊤ : ℕ∞) β := contDiff_const.div (hR.mul hs)
    (fun t => (mul_pos (hRpos t) (hspos t)).ne')
  have hRp : Function.Periodic R 1 := fun t => hr.2.1 t 0
  have hpp : Function.Periodic p 1 := periodic_deriv_real hRp
  have hsp : Function.Periodic s 1 := fun t => by dsimp only [s]; rw [hpp]
  have hαp : Function.Periodic α 1 := fun t => by dsimp only [α]; rw [hpp,hsp]
  have hβp : Function.Periodic β 1 := fun t => by dsimp only [β]; rw [hRp,hsp]
  obtain ⟨Rc,hRc,hRc',hbound⟩ := hr.revolution_radius_bound hangle
  obtain ⟨g,hg,hgp,hge⟩ := exists_periodic_local_identity hRc hRc'
  have heg (t a) : g (r (t,0)*(unitAngle a).re)=r (t,0)*(unitAngle a).re ∧
      g (r (t,0)*(unitAngle a).im)=r (t,0)*(unitAngle a).im := by
    have hz : ‖r (t,0) • unitAngle a‖=r (t,0) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hRpos t),unitAngle_norm,mul_one]
    have h₁ : |r (t,0)*(unitAngle a).re|≤Rc := by
      have hh := Complex.abs_re_le_norm (r (t,0) • unitAngle a)
      rw [hz] at hh
      have hh' : |r (t,0)*(unitAngle a).re| ≤ r (t,0) := by
        simpa only [Complex.smul_re,smul_eq_mul] using hh
      exact hh'.trans (hbound t)
    have h₂ : |r (t,0)*(unitAngle a).im|≤Rc := by
      have hh := Complex.abs_im_le_norm (r (t,0) • unitAngle a)
      rw [hz] at hh
      have hh' : |r (t,0)*(unitAngle a).im| ≤ r (t,0) := by
        simpa only [Complex.smul_im,smul_eq_mul] using hh
      exact hh'.trans (hbound t)
    exact ⟨(hge _ h₁).eq_of_nhds,(hge _ h₂).eq_of_nhds⟩
  have hed (t y) (hy : |y| < r (t,0)) : deriv g y=1 := by
    rw [(hge y (hy.le.trans (hbound t))).deriv_eq]
    exact deriv_id y
  have hb : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      ‖axisRadialField c α β g x‖≤1 :=
    hr.axisRadialField_boundary_bound hangle hαp hβp hgp heg (fun t =>
      (revolution_flux_coefficients_normal (p := p t) (hRpos t)).le)
  have hflux := isMinimizerAt_boundary_flux_le hV hE hm hμ
    (axisRadialField_contDiff c hα hβ hg) (axisRadialField_periodic c hαp hβp hgp) hb
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  rw [← setIntegral_congr_set (liftSet_congr_ae hae)] at hflux
  rw [hr.axisRadialField_flux hangle hα hβ hg hαp hβp hgp hed] at hflux
  have hId := periodic_revolution_flux_integral
    (fun t => (hR.differentiable (by simp) t).hasDerivAt) hp.continuous hRpos hRp hα hαp
    (fun _ => rfl) (fun _ => rfl)
  change (∫ t in (0 : ℝ)..1,R t^2*(deriv α t+2*β t))=_ at hId
  change Real.pi*(∫ t in (0 : ℝ)..1,R t^2*(deriv α t+2*β t))≤_ at hflux
  rw [hId] at hflux
  convert hflux using 1 <;> first | rfl | ring

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter_oai := @OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter_oai
