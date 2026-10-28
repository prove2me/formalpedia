-- Prove2me | solution 1 for OAI.CubicTorus.CenteredJacobiChart.classical_ground_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:48:35.861976+00:00
-- url     : https://prove2.me/submissions/50fe2947-6d5d-4585-b9ae-870040ad1542

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

end
end

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

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

lemma hyperplane_volume_zero {n : Cover} (hn : ‖n‖ = 1) :
    volume {x : Cover | ⟪n, x⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n, n⟫ = 0 at hm
  rw [real_inner_self_eq_norm_sq, hn] at hm
  norm_num at hm

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

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graphAreaVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ ^ 2 = 1 + ‖fderiv ℝ g y‖ ^ 2 := by
  rw [graphAreaVector, norm_sub_sq_real, hn, one_pow,
    normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn, plane_gradient_norm]
  ring

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

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

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

end CubicTorus

end
end

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
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

lemma graphMollifier_radius_tendsto :
    Tendsto (fun i ↦ (graphMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifier,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma graphSmooth_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    Tendsto (fun i ↦ graphSmooth (graphMollifier i) g y) atTop (𝓝 (g y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [mul_zero] using graphMollifier_radius_tendsto.const_mul (K:ℝ))
  exact graphSmooth_error _ hg y

theorem graphSmooth_fderiv_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ fderiv ℝ (graphSmooth (graphMollifier i) g) y)
      atTop (𝓝 (fderiv ℝ g y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi
  have ha := lipschitz_probability_average_hasFDerivAt (graphSmoothingMeasure_ac (graphMollifier i))
    hg (graphMollifier i).rOut_pos.le (graphSmoothingMeasure_radius (graphMollifier i)) y
  change dist (fderiv ℝ (fun z ↦ ∫ w, g (z-w) ∂graphSmoothingMeasure (graphMollifier i)) y) _ < ε
  rw [ha.2.fderiv,dist_eq_norm]
  have he : (∫ _w : Plane, fderiv ℝ g y ∂graphSmoothingMeasure (graphMollifier i)) = fderiv ℝ g y := by simp
  rw [← he,← integral_sub ha.1 (integrable_const _)]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have hb : (∫ w, ‖fderiv ℝ g (y-w)-fderiv ℝ g y‖ ∂graphSmoothingMeasure (graphMollifier i)) ≤ ε/2 := by
    calc
      _ ≤ ∫ _w : Plane, ε/2 ∂graphSmoothingMeasure (graphMollifier i) := by
        apply integral_mono_ae (ha.1.sub (integrable_const _)).norm (integrable_const _)
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with w hw
        have hh : dist (y-w) y < δ := by simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hw.trans_lt hi
        simpa only [dist_eq_norm,Pi.sub_apply] using (hclose hh).le
      _ = _ := by simp
  exact hb.trans_lt (by linarith)

lemma graphSmooth_gradient_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ gradient (graphSmooth (graphMollifier i) g) y) atTop (𝓝 (gradient g y)) := by
  exact ((InnerProductSpace.toDual ℝ Plane).symm.continuous.tendsto _).comp
    (graphSmooth_fderiv_tendsto hg hc)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_trace_volume_zero (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) :
    volume {x : Cover | ⟪n,x-a⟫ = graphHeightExtension a n g x} = 0 := by
  have hz : volume {x : Cover | ⟪n,x-a⟫ = 0} = 0 := by
    simpa only [Set.preimage_ofPred_eq,sub_eq_add_neg] using
      (measurePreserving_add_right volume (-a)).quasiMeasurePreserving.preimage_null
        (hyperplane_volume_zero hn)
  have hh := (graphShear_measurePreserving a hn hg.neg.measurable).quasiMeasurePreserving.preimage_null hz
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,graphShear,normalMove,graphHeightExtension,
    add_sub_right_comm,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,
    one_pow,mul_one,Pi.neg_apply]
  constructor <;> intro h <;> linarith

lemma measurable_graphSublevelIndicator (a n : Cover) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (graphSublevelIndicator a n g) := by
  exact measurable_const.indicator (measurableSet_lt (by fun_prop)
    (hg.comp ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const))))

lemma graphSublevelIndicator_bound (a n : Cover) (g : Plane → ℝ) (x : Cover) :
    |graphSublevelIndicator a n g x| ≤ 1 := by
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

lemma graphSublevelIndicator_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (a n : Cover) {x : Cover} (hx : ⟪n,x-a⟫ ≠ graphHeightExtension a n g x) :
    Tendsto (fun i ↦ graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphSublevelIndicator a n g x)) := by
  have ht := graphSmooth_tendsto hg (normalPlaneCoordinates n (x-a))
  have he : ∀ᶠ i in atTop,
      graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x = graphSublevelIndicator a n g x := by
    by_cases hl : ⟪n,x-a⟫ < graphHeightExtension a n g x
    · filter_upwards [ht.eventually (Ioi_mem_nhds hl)] with i hi
      change (if ⟪n,x-a⟫ < graphSmooth (graphMollifier i) g (normalPlaneCoordinates n (x-a)) then (1:ℝ) else 0) = _
      rw [ite_eq_left hi]
      exact (indicator_of_mem hl (fun _ ↦ (1:ℝ))).symm
    · have hh : graphHeightExtension a n g x < ⟪n,x-a⟫ := lt_of_le_of_ne (not_lt.mp hl) hx.symm
      filter_upwards [ht.eventually (Iio_mem_nhds hh)] with i hi
      have hi' : ¬ ⟪n,x-a⟫ < graphHeightExtension a n (graphSmooth (graphMollifier i) g) x := not_lt.mpr hi.le
      simp [graphSublevelIndicator,hl,hi']
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with i hi
  exact hi.symm

lemma graphSublevel_flux_mollification_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    Tendsto (fun i ↦ ∫ x : Cover, graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x * divergence F x)
      atTop (𝓝 (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x)) := by
  have hi : Integrable (divergence F) := (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖divergence F x‖)
    (fun i ↦ ((measurable_graphSublevelIndicator a n (graphSmooth_contDiff _ hg).continuous.measurable).mul
      (continuous_divergence hF).measurable).aestronglyMeasurable) hi.norm
  · intro i
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (graphSublevelIndicator_bound a n _ x)
  · have hae : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
      simpa only [ae_iff,not_not] using graph_trace_volume_zero a hn hg.continuous
    filter_upwards [hae] with x hx
    exact (graphSublevelIndicator_tendsto hg a n hx).mul_const _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_norm_linear {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphAreaVector n g y‖ ≤ 1+(K:ℝ) := by
  calc
    _ ≤ ‖n‖+‖normalPlaneEmbedding n (gradient g y)‖ := norm_sub_le _ _
    _ = 1+‖fderiv ℝ g y‖ := by rw [hn,normalPlaneEmbedding_norm,plane_gradient_norm]
    _ ≤ _ := add_le_add le_rfl (norm_fderiv_le_of_lipschitz ℝ hg)

lemma graph_trace_zero_outside {X : Type*} [Zero X] {a n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → X} {R : ℝ} (hs : tsupport F ⊆ Metric.closedBall a R)
    (g : Plane → ℝ) {y : Plane} (hy : y ∉ Metric.closedBall (0 : Plane) R) :
    F (a+normalGraph n g y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] at hh
  exact hy (by simpa only [Metric.mem_closedBall,dist_zero_right] using
    (normalGraph_norm_ge hn g y).trans hh)

theorem integral_C1graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hFs : HasCompactSupport F := (isCompact_closedBall a R).of_isClosed_subset isClosed_closure hs
  obtain ⟨M,hM⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hFs.norm
  have hMb (x : Cover) : ‖F x‖ ≤ M := hM (mem_range_self x)
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hMb 0)
  let B : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator (fun _ ↦ (1+(K:ℝ))*M)
  have hBi : Integrable B := (integrableOn_const (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have ht : Tendsto (fun i ↦ ∫ y : Plane,
      ⟪graphAreaVector n (graphSmooth (graphMollifier i) g) y,
        F (a+normalGraph n (graphSmooth (graphMollifier i) g) y)⟫) atTop
      (𝓝 (∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun i ↦ ((graphAreaVector_continuous n (graphSmooth_contDiff _ hg)).inner
        (graph_trace_continuous a n (graphSmooth_contDiff _ hg).continuous hF.continuous)).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · rw [show B y = (1+(K:ℝ))*M from indicator_of_mem hy _]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (graphAreaVector_norm_linear hn (graphSmooth_lipschitz _ hg) y)
            (hMb _) (norm_nonneg _) (by positivity))
      · rw [graph_trace_zero_outside hn hs _ hy,inner_zero_right,norm_zero,
          show B y = 0 from indicator_of_notMem hy _]
    · filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · have hd := graphSmooth_gradient_tendsto hg (hc y hy)
        have hnG : Tendsto (fun i ↦ normalGraph n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (normalGraph n g y)) :=
          tendsto_const_nhds.add ((graphSmooth_tendsto hg y).smul_const n)
        have hnA : Tendsto (fun i ↦ graphAreaVector n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (graphAreaVector n g y)) :=
          tendsto_const_nhds.sub (((normalPlaneLinearIsometry n).continuous.tendsto _).comp hd)
        exact hnA.inner ((hF.continuous.tendsto _).comp (tendsto_const_nhds.add hnG))
      · simp only [graph_trace_zero_outside hn hs _ hy,inner_zero_right]
        exact tendsto_const_nhds
  apply tendsto_nhds_unique (graphSublevel_flux_mollification_tendsto a hn hg hF hFs)
  simpa only [integral_graphSublevel_divergence a hn (graphSmooth_contDiff _ hg) hF hFs] using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_continuousAt (n : Cover) {g : Plane → ℝ} {y : Plane}
    (hc : ContinuousAt (fderiv ℝ g) y) : ContinuousAt (graphAreaVector n g) y := by
  exact continuousAt_const.sub ((normalPlaneLinearIsometry n).continuous.continuousAt.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hc))

lemma graph_weighted_continuous (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Continuous (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
  · exact (graph_trace_continuous a n hg hφ).continuousAt.mul (hψ y hy)
  · have he : (fun z : Plane ↦ φ (a+normalGraph n g z)*ψ z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [graph_trace_zero_outside hn hs _ hz,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma graph_weighted_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Integrable (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) :=
  (graph_weighted_continuous a hn hg hφ hs hψ).integrable_of_hasCompactSupport
    (graph_trace_compactSupport a hn hg hsφ).mul_right

lemma setIntegral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x in {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x}, divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  rw [← integral_C1graphSublevel_divergence a hn hg hc hF hs]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  rw [← integral_indicator hm]
  congr 1
  funext x
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

theorem blowup_graph_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA hm hgraph
      ((tsupport_smul_subset_left _ _).trans hφU),
    setIntegral_graphSublevel_divergence a hn hg hc hH
      ((tsupport_smul_subset_left _ _).trans hφR)] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_contDiff (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphUnitNormalExtension a n g) := by
  have hd := hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp hd
  exact (graphSlopeNormal_contDiff hn).comp (hgrad.comp
    ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma graphUnitNormalExtension_graph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g f : Plane → ℝ) (y : Plane) :
    graphUnitNormalExtension a n f (a+normalGraph n g y) = graphSlopeNormal n (gradient f y) := by
  unfold graphUnitNormalExtension
  rw [add_sub_cancel_left,normalGraph, map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]

lemma graphAreaVector_inner_unit {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪graphAreaVector n g y,graphSlopeNormal n (gradient g y)⟫ = ‖graphAreaVector n g y‖ := by
  have hh : 0 < ‖graphAreaVector n g y‖ := lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn _)
  rw [graphSlopeNormal,inner_smul_right,show n-normalPlaneEmbedding n (gradient g y)=graphAreaVector n g y from rfl,
    real_inner_self_eq_norm_sq]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_area_trace_mollified_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφ0 : ∀ x, 0 ≤ φ x) :
    Tendsto (fun i ↦ ∫ y : Plane, φ (a+normalGraph n g y)*
      ⟪graphAreaVector n g y,graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) (a+normalGraph n g y)⟫)
      atTop (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
  have hi := graph_weighted_integrable a hn hg.continuous hφ hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  apply tendsto_integral_of_dominated_convergence
    (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) ?_ hi
  · intro i
    filter_upwards [] with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    exact (norm_inner_le_norm _ _).trans_eq (by rw [graphUnitNormalExtension_unit a hn,mul_one])
  · filter_upwards [] with y
    by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
    · have ht : Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
          (a+normalGraph n g y)) atTop (𝓝 (graphSlopeNormal n (gradient g y))) := by
        simp only [graphUnitNormalExtension_graph a hn]
        exact ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp
          (graphSmooth_gradient_tendsto hg (hc y hy))
      simpa only [graphAreaVector_inner_unit hn] using ((show Tendsto (fun _ : ℕ ↦ graphAreaVector n g y) atTop
        (𝓝 (graphAreaVector n g y)) from tendsto_const_nhds).inner ht).const_mul (φ (a+normalGraph n g y))
    · simp only [graph_trace_zero_outside hn hφR _ hy,zero_mul]
      exact tendsto_const_nhds
  · intro i
    exact (graph_weighted_continuous a hn hg.continuous hφ hφR (fun y hy ↦
      (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous
          (graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)).continuous).continuousAt)).aestronglyMeasurable

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_normalCoverMap : Continuous normalCoverMap := by
  exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

lemma normalCoverMeasure_integral {μ : FiniteMeasure NormalBundle} {f : BlowupNormalBundle → ℝ}
    (hf : Continuous f) :
    (∫ z, f z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, f (normalCoverMap z) ∂(μ : Measure NormalBundle) := by
  rw [normalCoverMeasure,FiniteMeasure.toMeasure_map,
    integral_map continuous_normalCoverMap.measurable.aemeasurable hf.aestronglyMeasurable]

lemma normalMeasure_cutoff_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (O : Set Cover) : HasCutoffSaturation (normalCoverMeasure μ) O := by
  intro φ hφ hsφ hs hb C hC
  have hemass : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, φ (z.1 : Cover) ∂(μ : Measure NormalBundle) := by
    have hz : ∀ z : BlowupNormalBundle, z ∉ {z : BlowupNormalBundle | z.1 ∈ O} → φ z.1=0 :=
      fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact normalCoverMeasure_integral (hφ.continuous.comp continuous_fst)
  rw [hemass]
  apply normalMeasure_weighted_saturation hμ
    ⟨fun z ↦ φ (z.1 : Cover),hφ.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  intro F hF
  have hFc : Continuous F := hF.1.continuous
  have heflux : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun (z : BlowupNormalBundle) hz ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h)),zero_mul])]
    exact normalCoverMeasure_integral (by fun_prop)
  change (∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ C
  rw [← heflux]
  exact hC F hF.1 hF.2.2

lemma normalCoverMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ x in quotientMap ⁻¹' E, divergence F x := by
  rw [normalCoverMeasure_integral (by fun_prop)]
  change (∫ z : NormalBundle, ⟪(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
  rw [normalMeasure_local_flux hE hμ hF hc hs,← integral_indicator (hE.preimage measurable_quotientMap)]
  congr 1
  funext x
  classical
  by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiArea := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hiF (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound hnF z)
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤
        ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
      (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous hF.continuous).continuousAt)) hiArea
    intro y
    apply mul_le_mul_of_nonneg_left _ (hφb _).1
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnF _))
  refine le_antisymm ?_ ?_
  · exact hsat φ hφ hsφ hφO hφb _ hfield
  · apply le_of_tendsto (graph_area_trace_mollified_normal_tendsto a hn hg hc
      hφ.continuous hsφ hφR (fun x ↦ (hφb x).1))
    apply Eventually.of_forall
    intro i
    let F := graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
    have hnF (x : Cover) : ‖F x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
    rw [← blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (hiF F hF hnF) hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) (F z.1)).trans (by rw [z.2.property,one_mul]; exact hnF _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_signed_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfb : ∀ x, |f x| ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let ψ : Cover → ℝ := fun x ↦ φ x*((1+f x)/2)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul ((contDiff_const.add hf).div_const 2)
  have hsψ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_left
  have hψb (x : Cover) : ψ x ∈ Icc 0 1 := by
    have hx := abs_le.mp (hfb x)
    have hhalf : (1+f x)/2 ∈ Icc 0 1 := ⟨by linarith,by linarith⟩
    exact ⟨mul_nonneg (hφb x).1 hhalf.1,
      (mul_le_mul (hφb x).2 hhalf.2 hhalf.1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsψ' : HasCompactSupport ψ := hsφ.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hmψ := cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hψ hsψ'
    (hsψ.trans hφU) (hsψ.trans hφO) (hsψ.trans hφR) hψb
  have hmφ := cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb
  have hI (w : Cover → ℝ) (hw : Continuous w) (hb : ∀ x, w x ∈ Icc 0 1) :
      Integrable (fun z : BlowupNormalBundle ↦ w z.1) μ :=
    Integrable.of_bound (hw.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb _).1]; exact (hb _).2)
  have hGφ := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hGψ := graph_weighted_integrable a hn hg.continuous hψ.continuous hsψ' (hsψ.trans hφR)
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  calc
    (∫ z, φ z.1*f z.1 ∂μ) = ∫ z, (2*ψ z.1-φ z.1) ∂μ := by
      congr 1; funext z; dsimp only [ψ]; ring
    _ = 2*(∫ z, ψ z.1 ∂μ)-(∫ z, φ z.1 ∂μ) := by
      rw [integral_sub ((hI ψ hψ.continuous hψb).const_mul 2) (hI φ hφ.continuous hφb),integral_const_mul]
    _ = 2*(∫ y : Plane, ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by rw [hmψ,hmφ]
    _ = ∫ y : Plane, (2*(ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by
      rw [integral_sub (hGψ.const_mul 2) hGφ,integral_const_mul]
    _ = _ := by congr 1; funext y; dsimp only [ψ]; ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ConeSlopeReciprocalArea
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

lemma graph_superlevel_compl_ae {A U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : Continuous g)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫)) :
    ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ Aᶜ ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
  have hnz : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
    rw [ae_iff]
    simpa only [not_not] using graph_trace_volume_zero a hn hg
  filter_upwards [hgraph,hnz] with x hx hne hU
  rw [mem_compl_iff,hx hU,not_lt]
  exact ⟨fun h ↦ lt_of_le_of_ne h hne,le_of_lt⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialHeightCutoff_eventually_one {p : Cover} {r : ℝ} (hr : 0 < r)
    {x : Cover} (hx : x ∈ Metric.ball p r) :
    radialHeightCutoff p r =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
  exact radialHeightCutoff_one hr (Metric.ball_subset_closedBall hz)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
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

lemma graphAreaVector_norm_sqrt {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ = Real.sqrt (1+‖gradient g y‖^2) := by
  rw [plane_gradient_norm,← graphAreaVector_norm_sq hn g y,Real.sqrt_sq (norm_nonneg _)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

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

lemma C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma PlaneWeakGradient.unique {S : Set Plane} (hS : IsOpen S)
    {u : Plane → ℝ} {G H : Plane → Plane}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (huG : PlaneWeakGradient S u G) (huH : PlaneWeakGradient S u H) :
    G=ᵐ[volume.restrict S] H := by
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hG.sub hH).locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · change ∀ᵐ y ∂volume.restrict S, G y = H y
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [hz] with y hy hys
    exact sub_eq_zero.mp (hy hys)
  · have hiG := hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have hiH := hH.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    simp only [Pi.sub_apply,smul_sub,integral_sub hiG hiH]
    apply sub_eq_zero.mpr
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hiG v,← integral_inner hiH v]
    simp only [inner_smul_right]
    simp_rw [real_inner_comm (G _) v,real_inner_comm (H _) v]
    simpa only [mul_comm] using (huG v ψ hψ hc hs).trans (huH v ψ hψ hc hs).symm

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

lemma plane_gradient_div {a b : Plane → ℝ} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) (hby : b y≠0) :
    gradient (fun z ↦ a z/b z) y=
      (b y)⁻¹ • gradient a y-(a y/(b y)^2) • gradient b y := by
  apply ext_inner_right ℝ
  intro v
  have hi := (hasDerivAt_inv hby).comp_hasFDerivAt y hb.hasFDerivAt
  have hd := (ha.hasFDerivAt.mul hi).fderiv
  change fderiv ℝ (fun z ↦ a z*(b z)⁻¹) y=_ at hd
  simp only [div_eq_mul_inv,inner_gradient_left,inner_sub_left,real_inner_smul_left,hd,
    add_apply,smul_apply,smul_eq_mul,Function.comp_def]
  field_simp
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_inner_slope (p v : Plane) :
    ⟪p,cmcJacobian p v⟫=((cmcWeight p)^3)⁻¹*⟪p,v⟫ := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,real_inner_self_eq_norm_sq]
  have hs := cmcWeight_sq p
  have hn := (cmcWeight_pos p).ne'
  field_simp [hn]
  nlinarith [congrArg (fun r : ℝ ↦ r*⟪p,v⟫) hs]

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

lemma normalGraph_metric {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v w : Plane) :
    ⟪fderiv ℝ (normalGraph n g) y v,fderiv ℝ (normalGraph n g) y w⟫=
      ⟪v,w⟫+⟪gradient g y,v⟫*⟪gradient g y,w⟫ := by
  rw [normalGraph_fderiv_apply hg,normalGraph_fderiv_apply hg]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,mul_zero,add_zero]
  have ho : ⟪normalPlaneEmbedding n v,n⟫=0 := by rw [real_inner_comm]; exact normalPlaneEmbedding_inner hn v
  have hi := (normalPlaneLinearIsometry n).inner_map_map v w
  change ⟪normalPlaneEmbedding n v,normalPlaneEmbedding n w⟫=⟪v,w⟫ at hi
  simp only [hi,ho,mul_zero,zero_add,mul_one]
  ring

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_identity (p v w : Plane) :
    ⟪graphInverseMetric p v,w⟫+⟪p,graphInverseMetric p v⟫*⟪p,w⟫=⟪v,w⟫ := by
  simp only [graphInverseMetric,smul_apply,real_inner_smul_left,inner_smul_right]
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  simp only [inner_sub_left,real_inner_smul_left]
  field_simp [(cmcWeight_pos p).ne']
  ring

lemma graphTangentialGradient_inner {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (φ ψ : Plane → ℝ) (y : Plane) :
    ⟪graphTangentialGradient n g φ y,graphTangentialGradient n g ψ y⟫=
      cmcWeight (gradient g y)*⟪gradient φ y,cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
  unfold graphTangentialGradient
  rw [normalGraph_metric hn hg,graphInverseMetric_identity]
  simp only [graphInverseMetric,smul_apply,inner_smul_right]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_slope (p q : Plane) (c : ℝ) :
    graphInverseMetric p (q+c • p)=q+
      ((c-⟪p,q⟫)/(cmcWeight p)^2) • p := by
  rw [graphInverseMetric,smul_apply,cmcJacobian_apply]
  simp only [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,smul_sub,smul_smul,
    mul_inv_cancel₀ (cmcWeight_pos p).ne',one_smul]
  have he : c-cmcWeight p*(((cmcWeight p)^3)⁻¹*(⟪p,q⟫+c*‖p‖^2))=
      (c-⟪p,q⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ c*r) (cmcWeight_sq p)]
  rw [add_sub_assoc,← sub_smul,he]

lemma graph_metric_projection {n : Cover} (hn : ‖n‖=1) (p : Plane) (v : Cover) :
    normalPlaneEmbedding n (graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p))+
      ⟪p,graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p)⟫ • n=
        v-⟪graphSlopeNormal n p,v⟫ • graphSlopeNormal n p := by
  have he : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  have hi : ⟪graphSlopeNormal n p,v⟫=(cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫) := by
    rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
  have hc : ⟪p,normalPlaneCoordinates n v⟫+
      ((⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2)*‖p‖^2=
        ⟪n,v⟫-(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*r) (cmcWeight_sq p)]
  rw [graphInverseMetric_slope,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hc,
    he,map_add,map_smul,hi,graphSlopeNormal_weight hn]
  have hr := normalPlaneCoordinates_reconstruct hn v
  change (normalPlaneLinearIsometry n).toContinuousLinearMap (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v at hr
  conv_rhs => lhs; rw [← hr]

  have hq : (cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*(cmcWeight p)⁻¹=
      (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp
  simp only [smul_smul,smul_sub,hq,sub_smul,he]
  module

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SmoothScalarSeparatedTrunc
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

lemma surfaceCutoffJet_continuous (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    Continuous (surfaceCutoffJet μ f) := by
  unfold surfaceCutoffJet
  fun_prop

lemma surfaceCutoffJet_smooth (μ : FiniteMeasure NormalBundle) (f g : smoothPeriodicScalars) :
    surfaceCutoffJet μ f (surfaceSmoothJet μ g)=surfaceSmoothJet μ (smoothScalarMul f g) := by
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let df := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  have hq := (smoothScalarValue f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdf := (smoothScalarGradient f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarValue g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdg := (smoothScalarGradient g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hfg := (smoothScalarValue (smoothScalarMul f g)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdfg := (smoothScalarGradient (smoothScalarMul f g)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ g).1,hq,hg,hfg] with z hz hqz hgz hfgz
    change (q • (surfaceSmoothJet μ g).1 : Lp ℝ 2 (μ : Measure NormalBundle)) z=_
    rw [hz]
    change q z * (surfaceSmoothJet μ g).1 z=_
    change q z=f.val z.1 at hqz
    change (surfaceSmoothJet μ g).1 z=g.val z.1 at hgz
    change (surfaceSmoothJet μ (smoothScalarMul f g)).1 z=f.val z.1*g.val z.1 at hfgz
    rw [hqz,hgz,hfgz]
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add (q • (surfaceSmoothJet μ g).2 : Lp Cover 2 (μ : Measure NormalBundle))
        ((surfaceSmoothJet μ g).1 • df),Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ g).2,
      Lp.coeFn_lpSMul (r := 2) (surfaceSmoothJet μ g).1 df,hq,hdf,hg,hdg,hdfg] with
      z hadd hfirst hsecond hqz hdfz hgz hdgz hdfgz
    change ((q • (surfaceSmoothJet μ g).2 : Lp Cover 2 (μ : Measure NormalBundle))+
      ((surfaceSmoothJet μ g).1 • df)) z=_
    rw [hadd,Pi.add_apply,hfirst,hsecond]
    change q z • (surfaceSmoothJet μ g).2 z+(surfaceSmoothJet μ g).1 z • df z=_
    change q z=f.val z.1 at hqz
    change df z=smoothScalarGradient f z at hdfz
    change (surfaceSmoothJet μ g).1 z=g.val z.1 at hgz
    change (surfaceSmoothJet μ g).2 z=smoothScalarGradient g z at hdgz
    change (surfaceSmoothJet μ (smoothScalarMul f g)).2 z=_ at hdfgz
    rw [hqz,hdfz,hgz,hdgz,hdfgz,smoothScalarGradient_mul,add_comm]

lemma surfaceCutoffJet_ae (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (surfaceCutoffJet μ f u).1 z=f.val z.1*u.1 z ∧
      (surfaceCutoffJet μ f u).2 z=f.val z.1 • u.2 z+u.1 z • smoothScalarGradient f z := by
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let df := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  filter_upwards [(smoothScalarValue f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q u.2,
    Lp.coeFn_lpSMul (r := 2) u.1 df,
    Lp.coeFn_add (q • u.2 : Lp Cover 2 (μ : Measure NormalBundle)) (u.1 • df)] with
    z hq hdf hv hw hd ha
  change q z=f.val z.1 at hq
  change df z=smoothScalarGradient f z at hdf
  constructor
  · change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z=_
    rw [hv]
    change q z*u.1 z=_
    rw [hq]
  · change ((q • u.2 : Lp Cover 2 (μ : Measure NormalBundle))+u.1 • df) z=_
    rw [ha,Pi.add_apply,hw,hd]
    change q z • u.2 z+u.1 z • df z=_
    rw [hq,hdf]

theorem surfaceCutoffJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    surfaceCutoffJet μ f u∈surfaceH1 μ := by
  apply map_mem_closure (surfaceCutoffJet_continuous μ f) hu
  rintro _ ⟨g,rfl⟩
  rw [surfaceCutoffJet_smooth]
  exact ⟨smoothScalarMul f g,rfl⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace CubicTorus

theorem measure_eq_of_smooth_bounded_integrals
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ,ContDiff ℝ (⊤ : ℕ∞) f → (∀ x,|f x|≤1) →
      (∫ x,f x ∂μ)=∫ x,f x ∂ν) : μ=ν := by
  apply Measure.ext_of_charFun
  funext t
  apply Complex.ext
  · change RCLike.re (charFun μ t)=RCLike.re (charFun ν t)
    rw [charFun_apply,charFun_apply,← integral_re (𝕜 := ℂ),← integral_re (𝕜 := ℂ)]
    · simpa only [RCLike.re_to_complex,Complex.exp_re,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,Real.exp_zero,one_mul] using
        h (fun x ↦ Real.cos ⟪x,t⟫) (contDiff_id.inner ℝ contDiff_const).cos
          (fun x ↦ Real.abs_cos_le_one _)
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
  · change RCLike.im (charFun μ t)=RCLike.im (charFun ν t)
    rw [charFun_apply,charFun_apply,← integral_im (𝕜 := ℂ),← integral_im (𝕜 := ℂ)]
    · simpa only [RCLike.im_to_complex,Complex.exp_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,mul_one,zero_add,add_zero,Real.exp_zero,one_mul] using
        h (fun x ↦ Real.sin ⟪x,t⟫) (contDiff_id.inner ℝ contDiff_const).sin
          (fun x ↦ Real.abs_sin_le_one _)
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _
    · exact (BoundedContinuousFunction.innerProbChar t).integrable _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_measure_eq {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    Measure.map (fun z : BlowupNormalBundle ↦ z.1)
      (((ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}).withDensity
        (fun z ↦ ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane ↦ a+normalGraph n g y)
      (volume.withDensity (fun y : Plane ↦
        ENNReal.ofReal (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1∈O}
  let G : Plane → Cover := fun y ↦ a+normalGraph n g y
  let w : Plane → ℝ := fun y ↦ φ (G y)*‖graphAreaVector n g y‖
  have hGc : Continuous G := graph_trace_continuous a n hg.continuous continuous_id
  have hwc : Continuous w := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hwi : Integrable w := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hφi : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  let : IsFiniteMeasure (μ.withDensity (fun z : BlowupNormalBundle ↦ ENNReal.ofReal (φ z.1))) :=
    isFiniteMeasure_withDensity_ofReal hφi.hasFiniteIntegral
  let : IsFiniteMeasure (volume.withDensity (fun y : Plane ↦ ENNReal.ofReal (w y))) :=
    isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  change Measure.map (fun z : BlowupNormalBundle ↦ z.1)
    (μ.withDensity (fun z ↦ ENNReal.ofReal (φ z.1))) =
    Measure.map G (volume.withDensity (fun y ↦ ENNReal.ofReal (w y)))
  apply measure_eq_of_smooth_bounded_integrals
  intro f hf hfb
  have hmφ : Measurable (fun z : BlowupNormalBundle ↦ ENNReal.ofReal (φ z.1)) :=
    (hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal
  rw [integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_map hGc.measurable.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hmφ
      (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hwc.measurable.ennreal_ofReal
      (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hwpos (y : Plane) : 0≤w y := mul_nonneg (hφb (G y)).1 (norm_nonneg _)
  simp_rw [ENNReal.toReal_ofReal (hφb _).1,ENNReal.toReal_ofReal (hwpos _),smul_eq_mul]
  have he := cutoff_graph_patch_signed_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb hf hfb
  change (∫ z,φ z.1*f z.1 ∂μ)=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all volume fun y ↦ by dsimp only [w,G]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map f (μ.withDensity (w ∘ f))=(Measure.map f μ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs,
    Measure.restrict_map hf hs,lintegral_map hw hf]
  rfl

lemma projected_cutoff_measure {ν : Measure BlowupNormalBundle} {O : Set Cover}
    (hO : MeasurableSet O) {φ : Cover → ℝ} (hφ : Measurable φ) :
    Measure.map Prod.fst ((ν.restrict {z | z.1∈O}).withDensity
      (fun z ↦ ENNReal.ofReal (φ z.1)))=
      ((Measure.map Prod.fst ν).restrict O).withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
  change Measure.map Prod.fst ((ν.restrict (Prod.fst ⁻¹' O)).withDensity
    ((fun x ↦ ENNReal.ofReal (φ x)) ∘ Prod.fst))=_
  rw [sibling_map_withDensity_comp _ measurable_fst hφ.ennreal_ofReal,
    ← Measure.restrict_map measurable_fst hO]

lemma normalCoverMeasure_reverse_projected (μ : FiniteMeasure NormalBundle) :
    Measure.map Prod.fst (normalCoverMeasure (μ.map reverseNormal) : Measure BlowupNormalBundle)=
      Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle) := by
  simp only [normalCoverMeasure,FiniteMeasure.toMeasure_map]
  rw [Measure.map_map continuous_normalCoverMap.measurable continuous_reverseNormal.measurable,
    Measure.map_map measurable_fst
      (continuous_normalCoverMap.measurable.comp continuous_reverseNormal.measurable),
    Measure.map_map measurable_fst continuous_normalCoverMap.measurable]
  rfl

theorem normalMeasure_graph_patch_measure_eq {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1) :
    ((Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle)).restrict
      {x | ∀ i,0<x i ∧ x i<1}).withDensity (fun x ↦ ENNReal.ofReal (φ x))=
    Measure.map (fun y : Plane ↦ a+normalGraph n g y)
      (volume.withDensity (fun y : Plane ↦
        ENNReal.ofReal (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  have hO : MeasurableSet {x : Cover | ∀ i,0<x i ∧ x i<1} := by measurability
  have hflux {F : Set Torus} (hF : MeasurableSet F) {η : FiniteMeasure NormalBundle}
      (hη : IsNormalMeasure F η) (X : Cover → Cover) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
      (hs : HasCompactSupport X) (hXO : tsupport X⊆{x | ∀ i,0<x i ∧ x i<1})
      (_hb : ∀ x,‖X x‖≤1) := normalCoverMeasure_local_flux hF hη hX hs hXO
  rcases hphase with hp|hp
  · have hp' : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x) := by
      simpa only [graphSignedHeight,sub_neg,mem_preimage] using hp
    have hm := cutoff_graph_patch_measure_eq (hE.preimage measurable_quotientMap)
      a hn hg hc hp' (normalMeasure_cutoff_saturation hμ _) (hflux hE hμ)
      hφ hsφ hφU hφO hφR hφb
    rwa [projected_cutoff_measure hO hφ.continuous.measurable] at hm
  · have hp' : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ graphHeightExtension a n g x<⟪n,x-a⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hp
    have hp'' := graph_superlevel_compl_ae a hn hg.continuous hp'
    have hμ' := isNormalMeasure_compl hE hμ
    have hm := cutoff_graph_patch_measure_eq (hE.compl.preimage measurable_quotientMap)
      a hn hg hc hp'' (normalMeasure_cutoff_saturation hμ' _) (hflux hE.compl hμ')
      hφ hsφ hφU hφO hφR hφb
    rwa [projected_cutoff_measure hO hφ.continuous.measurable,
      normalCoverMeasure_reverse_projected] at hm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CenteredJacobiChart
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

lemma integral_normal_cover_position (μ : FiniteMeasure NormalBundle)
    {k : Cover → ℝ} (hk : Measurable k) :
    (∫ x,k x ∂Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle))=
      ∫ z,k z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_map measurable_fst.aemeasurable hk.stronglyMeasurable.aestronglyMeasurable]
  change (∫ z,k z.1 ∂Measure.map normalCoverMap (μ : Measure NormalBundle))=_
  have hkm : Measurable (fun z : BlowupNormalBundle ↦ k z.1) := hk.comp measurable_fst
  rw [integral_map continuous_normalCoverMap.measurable.aemeasurable
    hkm.stronglyMeasurable.aestronglyMeasurable]
  rfl

theorem normalMeasure_graph_integral {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {k : Cover → ℝ} (hk : Measurable k) (hφk : ∀ x,φ x*k x=k x) :
    (∫ z,k z.1 ∂(μ : Measure NormalBundle))=
      ∫ y,‖graphAreaVector n g y‖*k (a+normalGraph n g y) := by
  let O : Set Cover := {x | ∀ i,0<x i ∧ x i<1}
  let ν := Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle)
  let X : Plane → Cover := fun y ↦ a+normalGraph n g y
  have hX : Measurable X := (graph_trace_continuous a n hg.continuous continuous_id).measurable
  have hw := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hm := normalMeasure_graph_patch_measure_eq hE hμ a hn hg hc hphase
    hφ hsφ hφU hφO hφR hφb
  have hi := congrArg (fun η : Measure Cover ↦ ∫ x,k x ∂η) hm
  rw [integral_withDensity_eq_integral_toReal_smul hφ.continuous.measurable.ennreal_ofReal
      (ae_of_all (ν.restrict O) fun _ ↦ ENNReal.ofReal_lt_top),
    integral_map hX.aemeasurable hk.stronglyMeasurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  simp_rw [ENNReal.toReal_ofReal (hφb _).1,
    ENNReal.toReal_ofReal (mul_nonneg (hφb _).1 (norm_nonneg _)),smul_eq_mul] at hi
  have hz (x : Cover) (hx : x∉O) : k x=0 := by
    have hnφ : x∉tsupport φ := fun h ↦ hx (hφO h)
    simpa only [image_eq_zero_of_notMem_tsupport hnφ,zero_mul] using (hφk x).symm
  change (∫ x in O,φ x*k x ∂ν)=_ at hi
  simp_rw [hφk] at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_normal_cover_position μ hk] at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with y
  calc
    φ (X y)*‖graphAreaVector n g y‖*k (X y)=
      ‖graphAreaVector n g y‖*(φ (X y)*k (X y)) := by ring
    _=_ := by rw [hφk]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSlopeNormal_inner_graphDerivative {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {y : Plane} (hg : DifferentiableAt ℝ g y) (w : Plane) :
    ⟪graphSlopeNormal n (gradient g y),fderiv ℝ (normalGraph n g) y w⟫=0 := by
  rw [(normalGraph_hasFDerivAt hg).fderiv]
  change ⟪graphSlopeNormal n (gradient g y),
    normalPlaneEmbedding n w+fderiv ℝ g y w•n⟫=0
  rw [graphSlopeNormal,real_inner_smul_left,inner_sub_left,inner_add_right,
    inner_add_right,real_inner_smul_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow]
  have hi : ⟪normalPlaneEmbedding n (gradient g y),normalPlaneEmbedding n w⟫=
      fderiv ℝ g y w := by
    rw [show normalPlaneEmbedding n (gradient g y)=normalPlaneLinearIsometry n (gradient g y) from rfl,
      show normalPlaneEmbedding n w=normalPlaneLinearIsometry n w from rfl,
      (normalPlaneLinearIsometry n).inner_map_map,inner_gradient_left]
  have hz : ⟪normalPlaneEmbedding n (gradient g y),n⟫=0 := by
    rw [real_inner_comm,normalPlaneEmbedding_inner hn]
  rw [hi,hz]
  ring

lemma normalGraph_translated_tangency {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Cover) (s : ℝ) (y w : Plane) :
    ⟪s•graphSlopeNormal n (gradient g y),
      fderiv ℝ (fun z ↦ x+normalGraph n g z) y w⟫=0 := by
  have hd := normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)
  rw [(hd.const_add x).fderiv,real_inner_smul_left]
  have ht := graphSlopeNormal_inner_graphDerivative hn (hg.differentiable (by simp) y) w
  rw [hd.fderiv] at ht
  rw [ht,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_trace_gradient (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Plane) :
    gradient (fun z ↦ F (a+normalGraph n g z)) y=
      normalPlaneCoordinates n (gradient F (a+normalGraph n g y))+
        ⟪n,gradient F (a+normalGraph n g y)⟫ • gradient g y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_add_left,real_inner_smul_left]
  have hX := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).const_add a
  have hd : fderiv ℝ (fun z ↦ F (a+normalGraph n g z)) y=
      (fderiv ℝ F (a+normalGraph n g y)).comp
        ((normalPlaneLinearIsometry n).toContinuousLinearMap+(fderiv ℝ g y).smulRight n) := by
    exact (hF.differentiable (by simp) _).hasFDerivAt.comp y hX |>.fderiv
  rw [hd]
  change fderiv ℝ F (a+normalGraph n g y)
    (normalPlaneEmbedding n v+fderiv ℝ g y v•n)=_
  rw [map_add,map_smul,← inner_gradient_left,← inner_gradient_left,
    real_inner_comm (gradient F _) n,← inner_gradient_left]
  congr 1
  · rw [real_inner_comm,normalPlaneEmbedding_inner_coordinates hn,real_inner_comm]
  · simp [smul_eq_mul,mul_comm]

theorem graphTangentialGradient_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Plane) :
    graphTangentialGradient n g (fun z ↦ F (a+normalGraph n g z)) y=
      gradient F (a+normalGraph n g y)-
        ⟪graphSlopeNormal n (gradient g y),gradient F (a+normalGraph n g y)⟫ •
          graphSlopeNormal n (gradient g y) := by
  rw [graphTangentialGradient,normalGraph_trace_gradient a hn hg hF,
    (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).fderiv]
  change normalPlaneEmbedding n _+fderiv ℝ g y _•n=_
  rw [← inner_gradient_left]
  exact graph_metric_projection hn _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem graph_compact_test_extension (a p : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {ρ : ℝ} (hρ : 0<ρ)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : ∀ y∈tsupport ψ,a+normalGraph n g y∈Metric.ball p (ρ/2)) :
    ∃ F : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      tsupport F⊆Metric.closedBall p ρ ∧
      (∀ y,F (a+normalGraph n g y)=ψ y) ∧
      (∀ y,F=ᶠ[𝓝 (a+normalGraph n g y)] graphHeightExtension a n ψ) := by
  let ζ := radialHeightCutoff p (ρ/2)
  let f := graphHeightExtension a n ψ
  let F : Cover → ℝ := fun x ↦ ζ x*f x
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := radialDensityWeight_contDiff _ _ _
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := graphHeightExtension_contDiff a n hψ
  have hsζ : HasCompactSupport ζ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hsb : tsupport ζ⊆Metric.closedBall p ρ := by
    have hh := radialDensityWeight_tsupport (a := p) (r := 2*(ρ/2))
      (ε := 3*(ρ/2)^2) (by positivity) (by positivity)
    convert hh using 1 <;> congr 1
    ring
  have hterm (y : Plane) : F=ᶠ[𝓝 (a+normalGraph n g y)] f := by
    let x := a+normalGraph n g y
    have hxy : normalPlaneCoordinates n (x-a)=y := by
      simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    by_cases hy : y∈tsupport ψ
    · have hz : ζ=ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) :=
        radialHeightCutoff_eventually_one (by positivity) (hsψ y hy)
      filter_upwards [hz] with z hz
      simp only [F,hz,one_mul]
    · have hψ0 : ψ=ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hy
      have ht : Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x) (𝓝 y) := by
        have ht := ((normalPlaneCoordinates n).continuous.comp
          (continuous_id.sub (continuous_const (y := a)))).tendsto x
        change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x)
          (𝓝 (normalPlaneCoordinates n (x-a))) at ht
        rwa [hxy] at ht
      have hf0 : f=ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := ht.eventually hψ0
      filter_upwards [hf0] with z hz
      simp only [F,hz,mul_zero]
  refine ⟨F,hζ.mul hf,hsζ.mul_right,tsupport_mul_subset_left.trans hsb,?_,hterm⟩
  intro y
  rw [(hterm y).eq_of_nhds]
  simp only [f,graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]

theorem compact_test_periodization {F : Cover → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsF : HasCompactSupport F)
    (hO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1}) :
    ∃ f : smoothPeriodicScalars,∀ x : CompactCell,
      f.val=ᶠ[𝓝 (x : Cover)] F := by
  refine ⟨⟨latticePeriodize F,latticePeriodize_contDiff hF hsF,latticePeriodize_periodic F⟩,?_⟩
  intro x
  exact latticePeriodize_eventuallyEq hsF hO (compactCell_coordinates x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_surfaceJacobiB_cutoff_commutator (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ)
    (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q u (surfaceCutoffJet μ f v)-
      surfaceJacobiB μ q v (surfaceCutoffJet μ f u)=
      ∫ z,⟪v.1 z • u.2 z-u.1 z • v.2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle) := by
  unfold surfaceJacobiB
  simp only [L2.inner_def]
  rw [← integral_sub (L2.integrable_inner u.2 (surfaceCutoffJet μ f v).2)
      (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceCutoffJet μ f v).1),
    ← integral_sub (L2.integrable_inner v.2 (surfaceCutoffJet μ f u).2)
      (L2.integrable_inner (surfaceMultiplier μ q v.1) (surfaceCutoffJet μ f u).1)]
  have hiu : Integrable (fun z : NormalBundle ↦
      ⟪u.2 z,(surfaceCutoffJet μ f v).2 z⟫-
      ⟪surfaceMultiplier μ q u.1 z,(surfaceCutoffJet μ f v).1 z⟫) (μ : Measure NormalBundle) :=
    (L2.integrable_inner u.2 (surfaceCutoffJet μ f v).2).sub
      (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceCutoffJet μ f v).1)
  have hiv : Integrable (fun z : NormalBundle ↦
      ⟪v.2 z,(surfaceCutoffJet μ f u).2 z⟫-
      ⟪surfaceMultiplier μ q v.1 z,(surfaceCutoffJet μ f u).1 z⟫) (μ : Measure NormalBundle) :=
    (L2.integrable_inner v.2 (surfaceCutoffJet μ f u).2).sub
      (L2.integrable_inner (surfaceMultiplier μ q v.1) (surfaceCutoffJet μ f u).1)
  rw [← integral_sub hiu hiv]
  apply integral_congr_ae
  filter_upwards [surfaceCutoffJet_ae μ f u,surfaceCutoffJet_ae μ f v,
    Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv hqu hqv
  change (surfaceMultiplier μ q u.1) z=q z*u.1 z at hqu
  change (surfaceMultiplier μ q v.1) z=q z*v.1 z at hqv
  rw [hu.1,hu.2,hv.1,hv.2,hqu,hqv]
  simp only [inner_add_right,inner_smul_right,inner_sub_left,real_inner_smul_left,
    RCLike.inner_apply,RCLike.conj_to_real]
  rw [real_inner_comm (v.2 z) (u.2 z)]
  ring

theorem surfaceH1_weak_wronskian (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u v : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hv : v∈surfaceH1 μ)
    (hju : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0)
    (hjv : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q v w=0)
    (f : smoothPeriodicScalars) :
    (∫ z,⟪v.1 z • u.2 z-u.1 z • v.2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle))=0 := by
  rw [← sibling_surfaceJacobiB_cutoff_commutator μ q u v f,
    hju _ (surfaceCutoffJet_mem_surfaceH1 μ f hv),
    hjv _ (surfaceCutoffJet_mem_surfaceH1 μ f hu),sub_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma spatialPullback_continuousMap (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : C(Torus,W)) :
    spatialPullback μ W (ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F)=
      ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        (F.comp ⟨normalProjection,normalProjection_continuous⟩) := by
  apply Lp.ext
  have hF := F.coeFn_toLp (p := 2) (𝕜 := ℝ) (spatialNormalMeasure μ : Measure Torus)
  have hFp := ae_of_ae_map normalProjection_continuous.measurable.aemeasurable hF
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F)
    (normalProjection_measurePreserving μ),hFp,
    (F.comp ⟨normalProjection,normalProjection_continuous⟩).coeFn_toLp
      (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

lemma surfaceSmoothJet_value_spatial (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    (surfaceSmoothJet μ f).1∈Set.range (spatialPullback μ ℝ) := by
  let F : C(Torus,ℝ) := ⟨fun a ↦ f.val (representative a),
    continuous_periodic_descent f.property.1.continuous f.property.2⟩
  refine ⟨ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F,?_⟩
  rw [spatialPullback_continuousMap]
  congr 1
  apply ContinuousMap.ext
  intro z
  exact periodic_representative f.property.2 z.1

lemma surfaceSmoothJet_gradient_spatial {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (f : smoothPeriodicScalars) :
    (surfaceSmoothJet μ f).2∈Set.range (spatialPullback μ Cover) := by
  let F₀ : Cover → Cover := fun x ↦
    gradient f.val x-⟪N x,gradient f.val x⟫ • N x
  have hF₀ : Continuous F₀ := by
    have hg := (gradient_contDiff f.property.1).continuous
    exact hg.sub ((hN.inner (𝕜 := ℝ) hg).smul hN)
  have hFp (m) (x) : F₀ (x+latticeVector m)=F₀ x := by
    simp only [F₀,hp,gradient_periodic f.property.2]
  let F : C(Torus,Cover) := ⟨fun a ↦ F₀ (representative a),continuous_periodic_descent hF₀ hFp⟩
  refine ⟨ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F,?_⟩
  rw [spatialPullback_continuousMap]
  apply Lp.ext
  filter_upwards [(F.comp ⟨normalProjection,normalProjection_continuous⟩).coeFn_toLp
    (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),hn]
    with z h₁ h₂ h₃
  rw [h₁]
  change _=(surfaceSmoothJet μ f).2 z
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at h₂
  rw [h₂]
  change F₀ (representative (quotientMap z.1))=_
  rw [periodic_representative hFp]
  change gradient f.val z.1-⟪N z.1,gradient f.val z.1⟫ • N z.1=_
  rw [h₃]
  rfl

theorem surfaceH1_spatial_descent {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
      (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus)),
      spatialPullback μ ℝ v=u.1 ∧ spatialPullback μ Cover G=u.2 := by
  have hv : IsClosed (Set.range (spatialPullback μ ℝ)) :=
    (spatialPullback μ ℝ).isometry.isClosedEmbedding.isClosed_range
  have hg : IsClosed (Set.range (spatialPullback μ Cover)) :=
    (spatialPullback μ Cover).isometry.isClosedEmbedding.isClosed_range
  have hs : IsClosed {w : SurfaceJet μ | w.1∈Set.range (spatialPullback μ ℝ) ∧
      w.2∈Set.range (spatialPullback μ Cover)} :=
    (hv.preimage continuous_fst).inter (hg.preimage continuous_snd)
  have hr : Set.range (surfaceSmoothJet μ)⊆{w : SurfaceJet μ |
      w.1∈Set.range (spatialPullback μ ℝ) ∧ w.2∈Set.range (spatialPullback μ Cover)} := by
    rintro _ ⟨f,rfl⟩
    exact ⟨surfaceSmoothJet_value_spatial μ f,surfaceSmoothJet_gradient_spatial hN hp hn f⟩
  obtain ⟨⟨v,hv⟩,⟨G,hG⟩⟩ := closure_minimal hr hs hu
  exact ⟨v,G,hv,hG⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma dominatedL2Pullback_ae {α β W : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ν : Measure α) (μ : Measure β) (f : α → β) (hf : Measurable f)
    {C : ℝ≥0∞} (hC : C≠⊤) (hdom : Measure.map f ν≤C•μ) (u : Lp W 2 μ) :
    dominatedL2Pullback ν μ f hf hC hdom u =ᵐ[ν] fun x ↦ u (f x) := by
  have h := Lp.coeFn_LpToLpOfMeasureLeSMul hC hdom u
  have hp := ae_of_ae_map hf.aemeasurable h
  have hc := Lp.coeFn_compMeasurePreserving (Lp.LpToLpOfMeasureLeSMul hC hdom u)
    (show MeasurePreserving f ν (Measure.map f ν) from ⟨hf,rfl⟩)
  exact hc.trans hp

lemma surfaceChartPullback_continuousMap (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (F : Plane → Torus) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map F (volume.restrict D)≤C•(spatialNormalMeasure μ : Measure Torus))
    (f : C(Torus,W)) :
    surfaceChartPullback μ W D F hF hC hdom
      (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        (f.comp ⟨normalProjection,normalProjection_continuous⟩))
      =ᵐ[volume.restrict D] fun x ↦ f (F x) := by
  rw [← spatialPullback_continuousMap]
  change dominatedL2Pullback (volume.restrict D) (spatialNormalMeasure μ : Measure Torus)
    F hF hC hdom (spatialPushdown μ W (spatialPullback μ W _)) =ᵐ[_] _
  rw [spatialPushdown_pullback]
  refine (dominatedL2Pullback_ae _ _ _ _ _ _ _).trans ?_
  have ha := (Measure.absolutelyContinuous_of_le_smul hdom).ae_eq
    (f.coeFn_toLp (p := 2) (𝕜 := ℝ) (spatialNormalMeasure μ : Measure Torus))
  exact ae_of_ae_map hF.aemeasurable ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceH1_spatial_representatives {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
      (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus)),
      spatialPullback μ ℝ v=u.1 ∧ spatialPullback μ Cover G=u.2 ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
        u.2 z=G (quotientMap z.1)) := by
  obtain ⟨v,G,hv,hG⟩ := surfaceH1_spatial_descent hN hp hn hu
  refine ⟨v,G,hv,hG,?_⟩
  have h₁ := (Lp.coeFn_compMeasurePreserving v (normalProjection_measurePreserving μ))
  have h₂ := (Lp.coeFn_compMeasurePreserving G (normalProjection_measurePreserving μ))
  change spatialPullback μ ℝ v=ᵐ[_] _ at h₁
  change spatialPullback μ Cover G=ᵐ[_] _ at h₂
  rw [hv] at h₁
  rw [hG] at h₂
  exact h₁.and h₂

lemma continuous_normalProjectedGradient {N : Cover → Cover} (hN : Continuous N)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (normalProjectedGradient N F) := by
  have hG := (gradient_contDiff hF).continuous
  exact hG.sub ((hN.inner (𝕜 := ℝ) hG).smul hN)

theorem localized_wronskian_graph_integral {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {N : Cover → Cover} (hN : Continuous N)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hφF : ∀ x∈tsupport F,φ x=1)
    (f w : smoothPeriodicScalars) (hf : ∀ x : CompactCell,f.val=ᶠ[𝓝 (x : Cover)]F)
    (u : SurfaceJet μ)
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (haeu : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
      u.2 z=G (quotientMap z.1)) :
    (∫ z,⟪(surfaceSmoothJet μ w).1 z • u.2 z-
      u.1 z • (surfaceSmoothJet μ w).2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle))=
    ∫ y,‖graphAreaVector n g y‖*
      ⟪w.val (a+normalGraph n g y) • G (quotientMap (a+normalGraph n g y))-
        v (quotientMap (a+normalGraph n g y)) •
          normalProjectedGradient N w.val (a+normalGraph n g y),
          normalProjectedGradient N F (a+normalGraph n g y)⟫ := by
  let k : Cover → ℝ := fun x ↦ ⟪w.val x • G (quotientMap x)-
    v (quotientMap x) • normalProjectedGradient N w.val x,normalProjectedGradient N F x⟫
  have hk : Measurable k :=
    ((w.property.1.continuous.measurable.smul ((Lp.stronglyMeasurable G).measurable.comp measurable_quotientMap)).sub
      (((Lp.stronglyMeasurable v).measurable.comp measurable_quotientMap).smul
        (continuous_normalProjectedGradient hN w.property.1).measurable)).inner
          (continuous_normalProjectedGradient hN hF).measurable
  have hφk (x : Cover) : φ x*k x=k x := by
    by_cases hx : x∈tsupport F
    · rw [hφF x hx,one_mul]
    · have hz : gradient F x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp only [k,normalProjectedGradient,hz,inner_zero_right,zero_smul,sub_zero,mul_zero]
  calc
    _=(∫ z,k z.1 ∂(μ : Measure NormalBundle)) := by
      apply integral_congr_ae
      filter_upwards [haeu,haeN,
        (smoothScalarValue w).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
        (smoothScalarGradient w).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)]
        with z hu hNz hwv hwg
      change (surfaceSmoothJet μ w).1 z=w.val z.1 at hwv
      change (surfaceSmoothJet μ w).2 z=smoothScalarGradient w z at hwg
      rw [hwv,hwg,hu.1,hu.2]
      have hfgrad : gradient f.val (z.1 : Cover)=gradient F z.1 := by
        simp only [gradient,(hf z.1).fderiv_eq]
      change ⟪_,gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫•(z.2 : Cover)⟫=k z.1
      dsimp only [smoothScalarGradient,ContinuousMap.coe_mk]
      simp only [k,normalProjectedGradient,← hNz,hfgrad]
    _=_ := normalMeasure_graph_integral hE hμ a hn hg hc hphase hφ hsφ hφU hφO hφR hφb hk hφk

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjectedGradient_sign {N : Cover → Cover} {x n : Cover} {σ : ℝ}
    (hN : N x=σ•n) (hσ : σ=1 ∨ σ= -1) (F : Cover → ℝ) :
    normalProjectedGradient N F x=gradient F x-⟪n,gradient F x⟫•n := by
  rcases hσ with rfl|rfl
  · simp only [normalProjectedGradient,hN,one_smul]
  · simp only [normalProjectedGradient,hN,inner_neg_left,neg_smul,smul_neg,neg_neg,one_smul]

lemma normalProjectedGradient_graph_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {N : Cover → Cover} {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {y : Plane}
    (hNy : N (a+normalGraph n g y)=σ•graphSlopeNormal n (gradient g y))
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    normalProjectedGradient N F (a+normalGraph n g y)=
      graphTangentialGradient n g (fun z ↦ F (a+normalGraph n g z)) y := by
  rw [normalProjectedGradient_sign hNy hσ,graphTangentialGradient_trace a hn hg hF]

lemma plane_gradient_const_div {q : Plane → ℝ} {y : Plane}
    (hq : DifferentiableAt ℝ q y) (hy : q y≠0) (σ : ℝ) :
    gradient (fun z ↦ σ/q z) y= -(σ/(q y)^2)•gradient q y := by
  rw [plane_gradient_div (differentiableAt_const σ) hq hy]
  have hz : gradient (fun _ : Plane ↦ σ) y=0 := by simp [gradient]
  rw [hz,smul_zero,zero_sub,neg_smul]

theorem graph_wronskian_ground_state {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (a : Cover) (ψ : Plane → ℝ) (y : Plane) (σ u : ℝ) (G : Cover) :
    ‖graphAreaVector n g y‖*
      ⟪(σ/cmcWeight (gradient g y))•G-
          u•graphTangentialGradient n g (fun z ↦ σ/cmcWeight (gradient g z)) y,
        graphTangentialGradient n g ψ y⟫=
      σ*⟪cmcWeight (gradient g y)•(fderiv ℝ (fun z ↦ a+normalGraph n g z) y).adjoint G+
          u•gradient (fun z ↦ cmcWeight (gradient g z)) y,
        cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
  let q : Plane → ℝ := fun z ↦ cmcWeight (gradient g z)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  have hqy : q y≠0 := (cmcWeight_pos _).ne'
  have harea : ‖graphAreaVector n g y‖=q y := graphAreaVector_norm_sqrt hn g y
  have htr : fderiv ℝ (fun z ↦ a+normalGraph n g z) y=fderiv ℝ (normalGraph n g) y := by
    exact fderiv_const_add a
  rw [harea,inner_sub_left,real_inner_smul_left,real_inner_smul_left,
    graphTangentialGradient_inner hn hg,plane_gradient_const_div
      (hq.differentiable (by simp) y) hqy]
  have hide (V : Cover) : ⟪V,graphTangentialGradient n g ψ y⟫=
      q y*⟪(fderiv ℝ (normalGraph n g) y).adjoint V,
        cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
    rw [graphTangentialGradient,← ContinuousLinearMap.adjoint_inner_left,
      graphInverseMetric,smul_apply,inner_smul_right]
  rw [hide,htr]
  simp only [real_inner_smul_left,inner_add_left]
  change q y*((σ/q y)*(q y*_) -u*(q y*((-(σ/(q y)^2))*_)))=σ*(q y*_+u*_)
  field_simp
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphHeightExtension_eventually_zero (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g ψ : Plane → ℝ) {y : Plane} (hy : y∉tsupport ψ) :
    graphHeightExtension a n ψ=ᶠ[𝓝 (a+normalGraph n g y)] fun _ ↦ (0 : ℝ) := by
  have ht : Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a))
      (𝓝 (a+normalGraph n g y)) (𝓝 y) := by
    have ht := ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub (continuous_const (y := a)))).tendsto (a+normalGraph n g y)
    change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a))
      (𝓝 (a+normalGraph n g y)) (𝓝 (normalPlaneCoordinates n ((a+normalGraph n g y)-a))) at ht
    simpa only [add_sub_cancel_left,normalPlaneCoordinates_graph hn] using ht
  exact ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hy)

lemma gradient_eq_zero_of_graph_extension_germ (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g ψ : Plane → ℝ) {F : Cover → ℝ} {y : Plane}
    (hF : F=ᶠ[𝓝 (a+normalGraph n g y)] graphHeightExtension a n ψ)
    (hy : y∉tsupport ψ) : gradient F (a+normalGraph n g y)=0 := by
  have hg := hF.trans (graphHeightExtension_eventually_zero a hn g ψ hy)
  simp [gradient,hg.fderiv_eq]

lemma graphSlopeNormal_inner_axis {n : Cover} (hn : ‖n‖=1) (p : Plane) :
    ⟪n,graphSlopeNormal n p⟫=(cmcWeight p)⁻¹ := by
  rw [graphSlopeNormal_weight hn,inner_smul_right,inner_sub_right,
    real_inner_self_eq_norm_sq,hn,one_pow,normalPlaneEmbedding_inner hn,sub_zero,mul_one]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarWeakGradient
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

theorem CenteredJacobiChart.weak_ground_state_equation
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (haeu : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
      u.2 z=G (quotientMap z.1))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_hsψ : HasCompactSupport ψ)
    (htψ : tsupport ψ⊆Metric.ball 0 (c.r/2)) :
    (∫ y,⟪cmcWeight (gradient c.g y)•
      (fderiv ℝ (fun z ↦ cubeCenter+normalGraph c.n c.g z) y).adjoint
        (G (quotientMap (cubeCenter+normalGraph c.n c.g y)))+
      v (quotientMap (cubeCenter+normalGraph c.n c.g y))•
        gradient (fun z ↦ cmcWeight (gradient c.g z)) y,
      cmcJacobian (gradient c.g y) (gradient ψ y)⟫)=0 := by
  let X : Plane → Cover := fun y ↦ cubeCenter+normalGraph c.n c.g y
  let w := directionalNormalScalar N hN hp c.n
  have hsub : Metric.ball (0 : Plane) (c.r/2)⊆Metric.ball 0 c.r :=
    Metric.ball_subset_ball (by linarith [c.r_pos])
  obtain ⟨F,hF,hFc,hFs,hFt,hFg⟩ := graph_compact_test_extension cubeCenter cubeCenter
    c.n_unit c.g c.rho_pos hψ (fun y hy ↦ c.image_disk y (Metric.ball_subset_closedBall (hsub (htψ hy))))
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hFs.trans ((Metric.closedBall_subset_closedBall (by linarith [c.rho_pos])).trans
      (c.patch_in_U.trans c.U_in_cell))
  obtain ⟨f,hf⟩ := compact_test_periodization hF hFc hFO
  have hρ := c.rho_pos
  let φ := radialHeightCutoff cubeCenter c.ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hφc : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*c.ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφR : tsupport φ⊆Metric.closedBall cubeCenter c.R :=
    hφs.trans (c.patch_in_U.trans (c.U_in_ball.trans Metric.ball_subset_closedBall))
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hφF (x : Cover) (hx : x∈tsupport F) : φ x=1 :=
    radialHeightCutoff_one c.rho_pos (hFs hx)
  have hvw : surfaceSmoothJet μ w∈surfaceH1 μ :=
    (surfaceSmoothJet μ).range.le_topologicalClosure ⟨w,rfl⟩
  have hwr := surfaceH1_weak_wronskian μ q hu hvw hju hjw f
  have harea := localized_wronskian_graph_integral hE hμ cubeCenter c.n_unit c.lip
    (fun y _ ↦ (c.smooth.continuous_fderiv (by simp)).continuousAt) c.phase
    hφ hφc (hφs.trans c.patch_in_U) (hφs.trans (c.patch_in_U.trans c.U_in_cell))
    hφR hφb hN.continuous haeN hF hφF f w hf u v G haeu
  rw [harea] at hwr
  have he : (fun y ↦ ‖graphAreaVector c.n c.g y‖*
      ⟪w.val (X y) • G (quotientMap (X y))-
        v (quotientMap (X y)) • normalProjectedGradient N w.val (X y),
        normalProjectedGradient N F (X y)⟫)=
      fun y ↦ c.sign*⟪cmcWeight (gradient c.g y)•(fderiv ℝ X y).adjoint (G (quotientMap (X y)))+
        v (quotientMap (X y))•gradient (fun z ↦ cmcWeight (gradient c.g z)) y,
        cmcJacobian (gradient c.g y) (gradient ψ y)⟫ := by
    funext y
    by_cases hy : y∈Metric.ball (0 : Plane) c.r
    · have hnY := c.normal_disk y (Metric.ball_subset_closedBall hy)
      have ht : (fun z ↦ w.val (X z))=ᶠ[𝓝 y]
          fun z ↦ c.sign/cmcWeight (gradient c.g z) := by
        filter_upwards [Metric.isOpen_ball.eventually_mem hy] with z hz
        dsimp only [w,X]
        rw [directionalNormalScalar_apply]
        rw [c.normal_disk z (Metric.ball_subset_closedBall hz),inner_smul_right,
          graphSlopeNormal_inner_axis c.n_unit]
        exact (div_eq_mul_inv _ _).symm
      have hwv : w.val (X y)=c.sign/cmcWeight (gradient c.g y) := ht.eq_of_nhds
      have hwgrad : graphTangentialGradient c.n c.g (fun z ↦ w.val (X z)) y=
          graphTangentialGradient c.n c.g (fun z ↦ c.sign/cmcWeight (gradient c.g z)) y := by
        simp only [graphTangentialGradient,gradient,ht.fderiv_eq]
      have hψgrad : graphTangentialGradient c.n c.g (fun z ↦ F (X z)) y=
          graphTangentialGradient c.n c.g ψ y := by
        rw [show (fun z ↦ F (X z))=ψ from funext hFt]
      rw [normalProjectedGradient_graph_trace cubeCenter c.n_unit c.smooth c.sign_eq hnY w.property.1,
        normalProjectedGradient_graph_trace cubeCenter c.n_unit c.smooth c.sign_eq hnY hF,
        hwv,hwgrad,hψgrad]
      exact graph_wronskian_ground_state c.n_unit c.smooth cubeCenter ψ y c.sign
        (v (quotientMap (X y))) (G (quotientMap (X y)))
    · have hnψ : y∉tsupport ψ := fun h ↦ hy (hsub (htψ h))
      have hgF := gradient_eq_zero_of_graph_extension_germ cubeCenter c.n_unit c.g ψ (hFg y) hnψ
      have hgψ : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hnψ]
      simp only [normalProjectedGradient,X] at hgF ⊢
      rw [hgF,hgψ]
      simp only [inner_zero_right,zero_smul,sub_zero,map_zero,mul_zero]
  change (∫ y,(fun y ↦ ‖graphAreaVector c.n c.g y‖*_) y)=0 at hwr
  rw [he,integral_const_mul] at hwr
  have hsign : c.sign≠0 := by rcases c.sign_eq with h|h <;> rw [h] <;> norm_num
  exact (mul_eq_zero.mp hwr).resolve_left hsign

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceChartPullback_periodic (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (f : Cover → W) (hf : Continuous f) (hp : ∀ m x,f (x+latticeVector m)=f x) :
    surfaceChartPullback μ W D (fun y ↦ quotientMap (X y)) hX hC hdom
      (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        ⟨fun z ↦ f z.1,hf.comp (continuous_subtype_val.comp continuous_fst)⟩)
      =ᵐ[volume.restrict D] fun y ↦ f (X y) := by
  let F : C(Torus,W) := ⟨fun a ↦ f (representative a),continuous_periodic_descent hf hp⟩
  have h := surfaceChartPullback_continuousMap μ D (fun y ↦ quotientMap (X y)) hX hC hdom F
  have he : F.comp ⟨normalProjection,normalProjection_continuous⟩=
      (⟨fun z : NormalBundle ↦ f z.1,hf.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,W)) := by
    apply ContinuousMap.ext
    intro z
    exact periodic_representative hp z.1
  rw [he] at h
  exact h.trans (Filter.Eventually.of_forall (fun y ↦ periodic_representative hp (X y)))

lemma surfaceChartPullback_smoothJet_value (μ : FiniteMeasure NormalBundle)
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus)) (f : smoothPeriodicScalars) :
    surfaceChartPullback μ ℝ D (fun y ↦ quotientMap (X y)) hX hC hdom (surfaceSmoothJet μ f).1
      =ᵐ[volume.restrict D]fun y ↦ f.val (X y) :=
  surfaceChartPullback_periodic μ D X hX hC hdom f.val f.property.1.continuous f.property.2

lemma surfaceChartPullback_smoothJet_gradient {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus)) (f : smoothPeriodicScalars) :
    surfaceChartPullback μ Cover D (fun y ↦ quotientMap (X y)) hX hC hdom (surfaceSmoothJet μ f).2
      =ᵐ[volume.restrict D]fun y ↦ gradient f.val (X y)-
        ⟪N (X y),gradient f.val (X y)⟫•N (X y) := by
  let G : Cover → Cover := fun x ↦ gradient f.val x-⟪N x,gradient f.val x⟫•N x
  have hG : Continuous G := (gradient_contDiff f.property.1).continuous.sub
    ((hN.inner (𝕜 := ℝ) (gradient_contDiff f.property.1).continuous).smul hN)
  have hGp : ∀ m x,G (x+latticeVector m)=G x := by
    intro m x
    simp only [G,hp,gradient_periodic f.property.2]
  have he : (surfaceSmoothJet μ f).2=ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
      (⟨fun z : NormalBundle ↦ G z.1,hG.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,Cover)) := by
    apply Lp.ext
    filter_upwards [(smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
      (⟨fun z : NormalBundle ↦ G z.1,hG.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,Cover)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),hn]
      with z hz hgz hnz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hz
    rw [hz,hgz]
    change gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫•(z.2 : Cover)=G z.1
    simp only [G,hnz]
  rw [he]
  exact surfaceChartPullback_periodic μ D X hX hC hdom G hG hGp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_chart_weak_chain_rule {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (hD : MeasurableSet D) (X : Plane → Cover)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (htan : ∀ y∈D,∀ w : Plane,⟪N (X y),fderiv ℝ X y w⟫=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφD : tsupport φ⊆D) (w : Plane) :
    let F : Plane → Torus := fun y ↦ quotientMap (X y)
    let mF := (continuous_quotientMap.comp hX.continuous).measurable
    let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
    let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
    (∫ y in D,φ y*⟪G y,fderiv ℝ X y w⟫)=
      -(∫ y in D,fderiv ℝ φ y w*v y) := by
  let F : Plane → Torus := fun y ↦ quotientMap (X y)
  have mF : Measurable F := (continuous_quotientMap.comp hX.continuous).measurable
  let P := surfaceChartPullback μ ℝ D F mF hC hdom
  let Q := surfaceChartPullback μ Cover D F mF hC hdom
  let T₀ : Plane → Cover := fun y ↦ φ y•fderiv ℝ X y w
  let S₀ : Plane → ℝ := fun y ↦ fderiv ℝ φ y w
  have hT : MemLp T₀ 2 (volume.restrict D) :=
    (hφ.continuous.smul ((hX.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      hsφ.smul_right
  have hS : MemLp S₀ 2 (volume.restrict D) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hsφ.fderiv_apply ℝ w)
  let T := hT.toLp T₀
  let S := hS.toLp S₀
  let J : SurfaceJet μ → ℝ := fun v ↦ ⟪Q v.2,T⟫+⟪P v.1,S⟫
  have hJ : Continuous J :=
    ((Q.continuous.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).add
      ((P.continuous.comp continuous_fst).inner (𝕜 := ℝ) continuous_const)
  have hform (v : SurfaceJet μ) : J v=∫ y in D,
      (φ y*⟪Q v.2 y,fderiv ℝ X y w⟫+fderiv ℝ φ y w*P v.1 y) := by
    dsimp only [J]
    rw [L2.inner_def,L2.inner_def,← integral_add (L2.integrable_inner (Q v.2) T)
      (L2.integrable_inner (P v.1) S)]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp,hS.coeFn_toLp] with y hTy hSy
    change T y=T₀ y at hTy
    change S y=S₀ y at hSy
    simp only [hTy,hSy,T₀,S₀,real_inner_smul_right,RCLike.inner_apply,RCLike.conj_to_real]
  have hzero : ∀ f : smoothPeriodicScalars,J (surfaceSmoothJet μ f)=0 := by
    intro f
    have hx : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f.val (X y)) := f.property.1.comp hX
    let ψ : Plane → ℝ := fun y ↦ φ y*f.val (X y)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul hx
    have hsψ : HasCompactSupport ψ := hsφ.mul_right
    rw [hform]
    calc
      _=(∫ y in D,fderiv ℝ ψ y w) := by
        apply integral_congr_ae
        filter_upwards [surfaceChartPullback_smoothJet_value μ D X mF hC hdom f,
          surfaceChartPullback_smoothJet_gradient hN hp hn D X mF hC hdom f,
          ae_restrict_mem hD] with y hv hg hy
        change P (surfaceSmoothJet μ f).1 y=_ at hv
        change Q (surfaceSmoothJet μ f).2 y=_ at hg
        rw [hv,hg,inner_sub_left,real_inner_smul_left,htan y hy w,mul_zero,sub_zero,
          inner_gradient_left]
        have hdφ := hφ.differentiable (by simp) y
        have hdx := hx.differentiable (by simp) y
        have hdf := f.property.1.differentiable (by simp) (X y)
        have hdX := hX.differentiable (by simp) y
        change _=fderiv ℝ (φ*(fun z ↦ f.val (X z))) y w
        have hchain : fderiv ℝ (fun z ↦ f.val (X z)) y=
            (fderiv ℝ f.val (X y)).comp (fderiv ℝ X y) := fderiv_comp y hdf hdX
        rw [fderiv_mul hdφ hdx,hchain]
        simp only [add_apply,smul_apply,
          ContinuousLinearMap.comp_apply,smul_eq_mul]
        ring
      _=(∫ y,fderiv ℝ ψ y w) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by
          have hnψ : y∉tsupport ψ := fun he ↦ hy (hφD (tsupport_mul_subset_left he))
          rw [fderiv_of_notMem_tsupport ℝ hnψ,zero_apply])
      _=0 := integral_compact_fderiv_zero hψ hsψ w
  have hc : IsClosed {v : SurfaceJet μ | J v=0} := isClosed_eq hJ continuous_const
  have hr : Set.range (surfaceSmoothJet μ)⊆{v | J v=0} := by
    rintro _ ⟨f,rfl⟩
    exact hzero f
  have huJ : J u=0 := closure_minimal hr hc hu
  have hvform : ⟪P u.1,S⟫=(∫ y in D,fderiv ℝ φ y w*P u.1 y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp] with y hy
    change S y=S₀ y at hy
    simp only [hy,S₀,RCLike.inner_apply,RCLike.conj_to_real]
  have hgform : ⟪Q u.2,T⟫=(∫ y in D,φ y*⟪Q u.2 y,fderiv ℝ X y w⟫) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with y hy
    change T y=T₀ y at hy
    simp only [hy,T₀,real_inner_smul_right]
  change ⟪Q u.2,T⟫+⟪P u.1,S⟫=0 at huJ
  rw [hgform,hvform] at huJ
  exact eq_neg_of_add_eq_zero_left huJ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma memLp_variable_clm_on_compact {D : Set Plane} (hD : IsCompact D)
    {A : Plane → Cover →L[ℝ] Plane} (hA : Continuous A)
    (G : Lp Cover 2 (volume.restrict D)) :
    MemLp (fun y ↦ A y (G y)) 2 (volume.restrict D) := by
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hA.continuousOn
  have hm : AEStronglyMeasurable (fun y ↦ A y (G y)) (volume.restrict D) :=
    (show Continuous (fun p : (Cover →L[ℝ] Plane)×Cover ↦ p.1 p.2) from
      continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hA.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G))
  apply (Lp.memLp G).of_le_mul hm
  filter_upwards [ae_restrict_mem hD.measurableSet] with y hy
  exact ((A y).le_opNorm (G y)).trans (mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _))

theorem surfaceH1_hasPlanarWeakGradient {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (hD : IsCompact D) (X : Plane → Cover)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (htan : ∀ y∈D,∀ w : Plane,⟪N (X y),fderiv ℝ X y w⟫=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    let F : Plane → Torus := fun y ↦ quotientMap (X y)
    let mF := (continuous_quotientMap.comp hX.continuous).measurable
    let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
    let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
    HasPlanarWeakGradient D v (fun y ↦ (fderiv ℝ X y).adjoint (G y)) := by
  let F : Plane → Torus := fun y ↦ quotientMap (X y)
  have mF : Measurable F := (continuous_quotientMap.comp hX.continuous).measurable
  let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
  let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
  refine ⟨Lp.memLp v,memLp_variable_clm_on_compact hD
    (ContinuousLinearMap.adjoint.continuous.comp (hX.continuous_fderiv (by simp))) G,?_⟩
  intro φ hφ hsφ hφD w
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  exact surfaceH1_chart_weak_chain_rule hN hp hn D hD.measurableSet X hX hC hdom htan hu
    φ hφ hsφ hφD w

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma memLp_scalar_pair_integrable {u v : Plane → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun y ↦ u y*v y) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr
  filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with y hy hz
  simp only [hy,hz,RCLike.inner_apply,conj_trivial]
  ring

lemma memLp_vector_pair_integrable {u v : Plane → Plane}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun y ↦ ⟪u y,v y⟫) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr
  filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with y hy hz
  rw [hy,hz]

theorem PlaneWeakGradient.mul_smooth {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    PlaneWeakGradient S (fun y ↦ q y*u y)
      (fun y ↦ q y • G y+u y • gradient q y) := by
  intro v ψ hψ hc hs
  have hp := h v (fun y ↦ q y*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  have h₁ : Integrable (fun y ↦ ⟪G y,v⟫*(q y*ψ y)) := by
    have ht : MemLp (fun y ↦ (q y*ψ y) • v) 2 volume :=
      ((hq.continuous.mul hψ.continuous).smul continuous_const).memLp_of_hasCompactSupport
        hc.mul_left.smul_right
    simpa only [inner_smul_right,mul_comm] using memLp_vector_pair_integrable hG ht
  have h₂ : Integrable (fun y ↦ u y*(fderiv ℝ q y v*ψ y)) :=
    memLp_scalar_pair_integrable hu
      ((((hq.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).memLp_of_hasCompactSupport
        hc.mul_left)
  have h₃ : Integrable (fun y ↦ u y*(q y*fderiv ℝ ψ y v)) :=
    memLp_scalar_pair_integrable hu
      ((hq.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ v).mul_left)
  have hprod (y : Plane) : u y*fderiv ℝ (fun z ↦ q z*ψ z) y v=
      u y*(fderiv ℝ q y v*ψ y)+u y*(q y*fderiv ℝ ψ y v) := by
    rw [fderiv_fun_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  simp_rw [hprod] at hp
  rw [integral_add h₂ h₃] at hp
  have hleft (y : Plane) : ⟪q y • G y+u y • gradient q y,v⟫*ψ y=
      ⟪G y,v⟫*(q y*ψ y)+u y*(fderiv ℝ q y v*ψ y) := by
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left]
    ring
  simp_rw [hleft]
  rw [integral_add h₁ h₂]
  have hright : (∫ y,q y*u y*fderiv ℝ ψ y v)=(∫ y,u y*(q y*fderiv ℝ ψ y v)) := by
    congr 1; funext y; ring
  rw [hright]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma HasPlanarWeakGradient.extend_zero {D S : Set Plane} (hD : MeasurableSet D)
    {v : Plane → ℝ} {G : Plane → Plane} (h : HasPlanarWeakGradient D v G) (hSD : S⊆D) :
    PlaneWeakGradient S (D.indicator v) (D.indicator G) := by
  intro w ψ hψ hc hs
  have he := h.2.2 ψ hψ hc (hs.trans hSD) w
  have hl : (fun y ↦ ⟪D.indicator G y,w⟫*ψ y)=D.indicator (fun y ↦ ⟪G y,w⟫*ψ y) := by
    funext y
    by_cases hy : y∈D <;> simp [hy]
  have hr : (fun y ↦ D.indicator v y*fderiv ℝ ψ y w)=D.indicator (fun y ↦ v y*fderiv ℝ ψ y w) := by
    funext y
    by_cases hy : y∈D <;> simp [hy]
  rw [hl,hr,integral_indicator hD,integral_indicator hD]
  simpa only [mul_comm] using he

lemma HasPlanarWeakGradient.zero_extension_memLp {D : Set Plane} (hD : MeasurableSet D)
    {v : Plane → ℝ} {G : Plane → Plane} (h : HasPlanarWeakGradient D v G) :
    MemLp (D.indicator v) 2 volume ∧ MemLp (D.indicator G) 2 volume :=
  ⟨(memLp_indicator_iff_restrict hD).mpr h.1,(memLp_indicator_iff_restrict hD).mpr h.2.1⟩

lemma memLp_continuous_smul_zero_extension {D : Set Plane} (hD : IsCompact D)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {v : Plane → W} (hv : MemLp v 2 (volume.restrict D))
    {q : Plane → ℝ} (hq : Continuous q) :
    MemLp (fun y ↦ q y • D.indicator v y) 2 volume := by
  have hm : MemLp (D.indicator v) 2 volume := (memLp_indicator_iff_restrict hD.measurableSet).mpr hv
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hq.continuousOn
  apply hm.of_le_mul (c := B) (hq.aestronglyMeasurable.smul hm.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖q y • D.indicator v y‖≤B*‖D.indicator v y‖
  by_cases hy : y∈D
  · rw [Set.indicator_of_mem hy,norm_smul]
    exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hy,smul_zero,norm_zero,mul_zero,le_refl]

lemma memLp_zero_extension_smul_continuous {D : Set Plane} (hD : IsCompact D)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {v : Plane → ℝ} (hv : MemLp v 2 (volume.restrict D))
    {q : Plane → W} (hq : Continuous q) :
    MemLp (fun y ↦ D.indicator v y • q y) 2 volume := by
  have hm : MemLp (D.indicator v) 2 volume := (memLp_indicator_iff_restrict hD.measurableSet).mpr hv
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hq.continuousOn
  apply hm.of_le_mul (c := B) (hm.aestronglyMeasurable.smul hq.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖D.indicator v y • q y‖≤B*‖D.indicator v y‖
  by_cases hy : y∈D
  · rw [Set.indicator_of_mem hy,norm_smul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hy,zero_smul,norm_zero,mul_zero,le_refl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace CenteredJacobiChart
variable {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}

lemma weight_smooth (c : CenteredJacobiChart E μ N) : ContDiff ℝ (⊤ : ℕ∞) c.weight :=
  cmcWeight_contDiff.comp (plane_gradient_contDiff c.smooth)

lemma hasPlanarWeakGradient (c : CenteredJacobiChart E μ N)
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    HasPlanarWeakGradient (Metric.closedBall 0 c.r) (c.value u) (c.planarGradient u) := by
  apply surfaceH1_hasPlanarWeakGradient hN hp hae _ (isCompact_closedBall _ _)
    c.parameter c.parameter_smooth c.C_finite c.domination _ hu
  intro y hy w
  change ⟪N (cubeCenter+normalGraph c.n c.g y),fderiv ℝ c.parameter y w⟫=0
  rw [c.normal_disk y hy]
  exact normalGraph_translated_tangency c.n_unit c.smooth cubeCenter c.sign y w

lemma weighted_weak_gradient (c : CenteredJacobiChart E μ N)
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    MemLp (c.weightedValue u) 2 volume ∧ MemLp (c.weightedGradient u) 2 volume ∧
    PlaneWeakGradient (Metric.ball 0 (c.r/2)) (c.weightedValue u) (c.weightedGradient u) := by
  have hg := c.hasPlanarWeakGradient hN hp hae hu
  have hu0 := hg.zero_extension_memLp measurableSet_closedBall
  have hsub : Metric.ball (0 : Plane) (c.r/2)⊆Metric.closedBall 0 c.r :=
    (Metric.ball_subset_ball (by linarith [c.r_pos])).trans Metric.ball_subset_closedBall
  refine ⟨?_,?_,(hg.extend_zero measurableSet_closedBall hsub).mul_smooth hu0.1 hu0.2 c.weight_smooth⟩
  · exact memLp_continuous_smul_zero_extension (isCompact_closedBall _ _) hg.1 c.weight_smooth.continuous
  · exact (memLp_continuous_smul_zero_extension (isCompact_closedBall _ _) hg.2.1 c.weight_smooth.continuous).add
      (memLp_zero_extension_smul_continuous (isCompact_closedBall _ _) hg.1
        (plane_gradient_contDiff c.weight_smooth).continuous)

lemma representatives_ae (c : CenteredJacobiChart E μ N) {u : SurfaceJet μ}
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (hv : spatialPullback μ ℝ v=u.1) (hG : spatialPullback μ Cover G=u.2) :
    ∀ᵐ y ∂volume.restrict (Metric.closedBall (0 : Plane) c.r),
      c.value u y=v (quotientMap (c.parameter y)) ∧
      c.ambientGradient u y=G (quotientMap (c.parameter y)) := by
  have h₁ : c.value u=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      fun y ↦ v (quotientMap (c.parameter y)) := by
    unfold value surfaceChartPullback
    simp only [ContinuousLinearMap.comp_apply,← hv,spatialPushdown_pullback]
    exact dominatedL2Pullback_ae _ _ _ _ _ _ _
  have h₂ : c.ambientGradient u=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      fun y ↦ G (quotientMap (c.parameter y)) := by
    unfold ambientGradient surfaceChartPullback
    simp only [ContinuousLinearMap.comp_apply,← hG,spatialPushdown_pullback]
    exact dominatedL2Pullback_ae _ _ _ _ _ _ _
  exact h₁.and h₂

theorem weighted_divergence (c : CenteredJacobiChart E μ N)
    (hE : MeasurableSet E) (hμ : IsNormalMeasure E μ)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ⊆Metric.ball 0 (c.r/2)) :
    (∫ y,fderiv ℝ ψ y (cmcJacobian (gradient c.g y) (c.weightedGradient u y)))=0 := by
  obtain ⟨v,G,hv,hG,haeu⟩ := surfaceH1_spatial_representatives hN.continuous hp haeN hu
  have hw := c.weak_ground_state_equation hE hμ hN hp haeN q hu hju hjw v G haeu hψ hcψ hsψ
  rw [← hw]
  have ha := (ae_restrict_iff' measurableSet_closedBall).mp (c.representatives_ae v G hv hG)
  apply integral_congr_ae
  filter_upwards [ha] with y hy
  by_cases hys : y∈Metric.closedBall (0 : Plane) c.r
  · dsimp only [weightedGradient,planarGradient,weight]
    rw [Set.indicator_of_mem hys,Set.indicator_of_mem hys,(hy hys).1]
    dsimp only [planarGradient]
    rw [(hy hys).2,← inner_gradient_left,real_inner_comm,← cmcJacobian_symmetric]
    rfl
  · have hnt : y∉tsupport ψ := by
      intro ht
      apply hys
      exact Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith [c.r_pos]) (hsψ ht))
    have hd : fderiv ℝ ψ y=0 := fderiv_of_notMem_tsupport ℝ hnt
    have hg : gradient ψ y=0 := by simp [gradient,hd]
    rw [hd,hg]
    simp only [zero_apply,map_zero,inner_zero_right]

end CenteredJacobiChart
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NodalTorusScalar
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

lemma CenteredJacobiChart.scalar_representative_ae
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    {F : Torus → ℝ} (hF : Measurable F)
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z)) :
    (fun y ↦ F (quotientMap (c.parameter y)))=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      c.value u := by
  obtain ⟨v,G,hv,hG,haeu⟩ := surfaceH1_spatial_representatives hN hp haeN hu
  have hsp : F=ᵐ[(spatialNormalMeasure μ : Measure Torus)] v := by
    apply (ae_map_iff normalProjection_continuous.measurable.aemeasurable
      (measurableSet_eq_fun hF (Lp.stronglyMeasurable v).measurable)).mpr
    filter_upwards [haeF,haeu] with z h₁ h₂
    exact h₁.symm.trans h₂.1
  have hmap := (Measure.absolutelyContinuous_of_le_smul c.domination).ae_eq hsp
  have hf := measurable_quotientMap.comp c.parameter_smooth.continuous.measurable
  have hchart := ae_of_ae_map hf.aemeasurable hmap
  filter_upwards [hchart,c.representatives_ae v G hv hG] with y h₁ h₂
  exact h₁.trans h₂.1.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma CenteredJacobiChart.smooth_scalar_ae
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (f : smoothPeriodicScalars) :
    (fun y ↦ f.val (c.parameter y))=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      c.value (surfaceSmoothJet μ f) := by
  have hf := c.scalar_representative_ae hN hp haeN (subset_closure (LinearMap.mem_range_self _ _))
    (continuous_periodic_descent f.property.1.continuous f.property.2).measurable
    (show ∀ᵐ z ∂(μ : Measure NormalBundle),(surfaceSmoothJet μ f).1 z=
      f.val (representative (normalProjection z)) from by
      filter_upwards [(smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz
      change (surfaceSmoothJet μ f).1 z=f.val z.1 at hz
      rw [hz]
      exact (periodic_representative f.property.2 z.1).symm)
  simpa only [periodic_representative f.property.2] using hf

theorem CenteredJacobiChart.classical_ground_state_oai
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0) :
    ∀ y∈Metric.ball (0 : Plane) (c.r/2),
      planeDivergence (fun z ↦ cmcJacobian (gradient c.g z)
        (gradient (fun w ↦ c.weight w*f.val (c.parameter w)) z)) y=0 := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  let u := surfaceSmoothJet μ f
  have hu : u∈surfaceH1 μ := subset_closure (LinearMap.mem_range_self _ _)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  obtain ⟨huL,hGL,hw⟩ := c.weighted_weak_gradient hN.continuous hp haeN hu
  have he := (ae_restrict_iff' measurableSet_closedBall).mp (c.smooth_scalar_ae hN.continuous hp haeN f)
  have hFe : F=ᵐ[volume.restrict (Metric.ball (0 : Plane) (c.r/2))] c.weightedValue u := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [he] with y hy hys
    have hD : y∈Metric.closedBall (0 : Plane) c.r :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith [c.r_pos]) hys)
    simp only [F,CenteredJacobiChart.weightedValue,Set.indicator_of_mem hD,hy hD,u]
  have hW : PlaneWeakGradient (Metric.ball (0 : Plane) (c.r/2)) F (c.weightedGradient u) :=
    hw.local_congr measurableSet_ball hFe EventuallyEq.rfl
  have hGe := PlaneWeakGradient.unique Metric.isOpen_ball (hGL.locallyIntegrable (by norm_num))
    (plane_gradient_contDiff hF).continuous.locallyIntegrable hW
    (C1_weak_gradient (hF.of_le (by simp)) _)
  apply LinearCMCEquation.classical_zero c.smooth hF Metric.isOpen_ball
  intro ψ hψ hc hs
  have hd := c.weighted_divergence hE hμ hN hp haeN q hu hjf hjw hψ hc hs
  simp only [sub_zero]
  rw [← hd]
  apply integral_congr_ae
  have hGe' := (ae_restrict_iff' measurableSet_ball).mp hGe
  filter_upwards [hGe'] with y hy
  by_cases hys : y∈Metric.ball (0 : Plane) (c.r/2)
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun ht ↦ hys (hs ht))]
    rfl

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.CenteredJacobiChart.classical_ground_state_oai := @OAI.CubicTorus.CenteredJacobiChart.classical_ground_state_oai
