-- Prove2me | solution 1 for OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:31:33.878807+00:00
-- url     : https://prove2.me/submissions/548f7906-b965-47aa-b8e4-b0a3000495ff

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_cmc_linearized_holder_gradient

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

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  simpa only [mollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma fderiv_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x v : X) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v)) x := by
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hs.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma real_convolution_comm (f g : X → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] f := by
  ext x
  rw [convolution_mul_swap, convolution_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ mul_comm _ _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
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

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_compact_norm_bound {Y : Type*} [NormedAddCommGroup Y]
    {g : X → Y} (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hs.norm
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

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

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

lemma cover_clm_component (L : Cover →L[ℝ] Cover) (v : Cover) (i : Fin 3) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma coverTrace_comp_comm (L M : Cover →L[ℝ] Cover) :
    coverTrace (L.comp M)=coverTrace (M.comp L) := by
  simp only [coverTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coverTrace_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    coverTrace (l.smulRight v)=l v := by
  conv_rhs => rw [cover_decompose v]
  simp only [coverTrace,ContinuousLinearMap.smulRight_apply,PiLp.smul_apply,
    smul_eq_mul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

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

lemma graphUnitNormalExtension_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {x : Cover}
    (hc : ContinuousAt (fderiv ℝ g) (normalPlaneCoordinates n (x-a))) :
    Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphUnitNormalExtension a n g x)) :=
  ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp (graphSmooth_gradient_tendsto hg hc)

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_norm_le (n x : Cover) : ‖normalPlaneCoordinates n x‖ ≤ ‖x‖ := by
  simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using
    (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0

lemma graph_weighted_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφR : tsupport φ ⊆ Metric.closedBall a R) (z : BlowupNormalBundle) :
    Tendsto (fun i ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n
      (graphSmooth (graphMollifier i) g) z.1⟫) atTop
      (𝓝 (φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)) := by
  by_cases hz : z.1 ∈ tsupport φ
  · have hcoord : normalPlaneCoordinates n (z.1-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hz)
    exact ((show Tendsto (fun _ : ℕ ↦ (z.2 : Cover)) atTop (𝓝 (z.2 : Cover)) from
      tendsto_const_nhds).inner (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hz,zero_mul]
    exact tendsto_const_nhds

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weighted_tendsto_on_tsupport {X : Type*} [TopologicalSpace X]
    {φ : X → ℝ} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : ∀ x ∈ tsupport φ, Tendsto (fun i ↦ f i x) atTop (𝓝 (g x))) (x : X) :
    Tendsto (fun i ↦ φ x*f i x) atTop (𝓝 (φ x*g x)) := by
  by_cases hx : x ∈ tsupport φ
  · exact (h x hx).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    exact tendsto_const_nhds

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

theorem cutoff_graph_patch_normal_ae {A O U : Set Cover} (hA : MeasurableSet A)
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
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let F : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let f : ℕ → BlowupNormalBundle → ℝ := fun i z ↦ φ z.1*⟪(z.2 : Cover),F i z.1⟫
  let f₀ : BlowupNormalBundle → ℝ := fun z ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hFn (i) (x) : ‖F i x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
  have hf (i) : AEStronglyMeasurable (f i) μ :=
    (show Continuous (f i) from (hφ.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd |>.inner ((hF i).continuous.comp continuous_fst))).aestronglyMeasurable
  have ht : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 (f₀ z)) :=
    ae_of_all μ (graph_weighted_normal_tendsto a hn hg hc hφR)
  have hb (i) (z : BlowupNormalBundle) : ‖f i z‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound (hFn i) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb₀ (z : BlowupNormalBundle) : ‖f₀ z‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound
      (fun x ↦ (graphUnitNormalExtension_unit a hn _ x).le) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hi₀ : Integrable f₀ μ := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hf ht) 1 (ae_of_all μ hb₀)
  have hilim : Tendsto (fun i ↦ ∫ z, f i z ∂μ) atTop (𝓝 (∫ z, f₀ z ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hf
      (integrable_const 1) (fun i ↦ ae_of_all μ (hb i)) ht
  have heint : (∫ z, f₀ z ∂μ) = ∫ z, φ z.1 ∂μ := by
    apply tendsto_nhds_unique hilim
    rw [show (∫ z, φ z.1 ∂μ) = _ from
      cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb]
    have hh := graph_area_trace_mollified_normal_tendsto a hn hg hc hφ.continuous hsφ hφR
      (fun x ↦ (hφb x).1)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb (hF i) (hFn i)
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hinon (z : BlowupNormalBundle) : 0 ≤ φ z.1-f₀ z := by
    have hh : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ ≤ 1 := by
      exact (real_inner_le_norm _ _).trans_eq (by rw [z.2.property,graphUnitNormalExtension_unit a hn,one_mul])
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hφb _).1 hh)
  have hezero : (∫ z, (φ z.1-f₀ z) ∂μ)=0 := by rw [integral_sub hiφ hi₀,heint,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hinon) (hiφ.sub hi₀)).mp hezero
  filter_upwards [hae] with z hz
  intro hzφ
  have hi : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ = 1 := by
    have hh : φ z.1*(1-⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)=0 := by
      simpa only [mul_sub,mul_one,f₀,Pi.zero_apply] using hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hzφ.ne')).symm
  exact (inner_eq_one_iff_of_norm_eq_one z.2.property (graphUnitNormalExtension_unit a hn g z.1)).mp hi

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_limit_mass {A O U : Set Cover} (hA : MeasurableSet A)
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
    {f : ℕ → Cover → ℝ} {f₀ : Cover → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (hfb : ∀ i x, |f i x| ≤ 1)
    (hlim : ∀ x ∈ tsupport φ, Tendsto (fun i ↦ f i x) atTop (𝓝 (f₀ x))) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f₀ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hleft : Tendsto (fun i ↦ ∫ z, φ z.1*f i z.1 ∂μ) atTop (𝓝 (∫ z, φ z.1*f₀ z.1 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ))
    · intro i
      exact ((hφ.continuous.mul (hf i).continuous).comp continuous_fst).aestronglyMeasurable
    · exact integrable_const 1
    · intro i
      filter_upwards [] with z
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs]
      exact (mul_le_mul (hφb _).2 (hfb i _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · exact ae_of_all μ fun z ↦ weighted_tendsto_on_tsupport hlim z.1
  have hright : Tendsto (fun i ↦ ∫ y : Plane,
      φ (a+normalGraph n g y)*f i (a+normalGraph n g y)*‖graphAreaVector n g y‖) atTop
      (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)
    · intro i
      have hh := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
      have hmeas : AEStronglyMeasurable (fun y : Plane ↦
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)*f i (a+normalGraph n g y))
          (volume : Measure Plane) :=
        (hh.mul (graph_trace_continuous a n hg.continuous (hf i).continuous)).aestronglyMeasurable
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hmeas
    · exact graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
    · intro i
      filter_upwards [] with y
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs,
        norm_norm]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hφb _).1 (hfb i _)) (norm_nonneg _)
    · filter_upwards [] with y
      exact (weighted_tendsto_on_tsupport hlim _).mul_const _
  apply tendsto_nhds_unique hleft
  convert hright using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact cutoff_graph_patch_signed_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb (hf i) (hfb i)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
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

lemma continuous_local_cutoff {f η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y*f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.mul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_vector_cutoff {f : Plane → Plane} {η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y • f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.smul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:Plane))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma compact_probability_average_integrable [NormedSpace ℝ F] [CompleteSpace F] {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) (b : ContDiffBump (0 : Plane)) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) := by
  obtain ⟨C,hC,hbound⟩ := continuous_compact_norm_bound hf hc
  exact Integrable.of_bound (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    C (Eventually.of_forall fun y ↦ hbound (x-y))

lemma compact_probability_average_uniform {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun i x ↦ ∫ y,f (x-y) ∂graphSmoothingMeasure (graphMollifier i)) f atTop := by
  have hu : UniformContinuous f := hf.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (half_pos hε)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi x
  have hfi := compact_probability_average_integrable hf hc (graphMollifier i) x
  have he : (∫ _y : Plane,f x ∂graphSmoothingMeasure (graphMollifier i))=f x := by simp
  rw [dist_comm,dist_eq_norm,← he,← integral_sub hfi (integrable_const _)]
  calc
    _ ≤ ∫ _y : Plane,ε/2 ∂graphSmoothingMeasure (graphMollifier i) :=
      norm_integral_le_of_norm_le (integrable_const _) (by
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with y hy
        have hd : dist (x-y) x<δ := by
          simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hy.trans_lt hi
        simpa only [dist_eq_norm] using (hclose hd).le)
    _ < ε := by simp; linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma test_kernel_support {R : ℝ} {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2))
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2) :
    tsupport (fun y ↦ b.normed volume (x-y))⊆Metric.ball 0 R := by
  have hs : tsupport (fun y ↦ b.normed volume (x-y))⊆
      (fun y ↦ x-y) ⁻¹' tsupport (b.normed volume) :=
    tsupport_comp_subset_preimage (f := fun y : Plane ↦ x-y) (b.normed volume)
      ((continuous_const : Continuous (fun _ : Plane ↦ x)).sub continuous_id)
  intro y hy
  have hh := hs hy
  have he : tsupport (b.normed (volume : Measure Plane))=Metric.closedBall 0 b.rOut :=
    b.tsupport_normed_eq
  change x-y∈tsupport (b.normed volume) at hh
  rw [he,Metric.mem_closedBall,dist_zero_right] at hh
  have hx' : ‖x‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  change dist y 0<R
  rw [dist_zero_right]
  calc
    ‖y‖ = ‖x-(x-y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖x‖+‖x-y‖ := norm_sub_le _ _
    _ < R/2+R/2 := add_lt_add hx' (hh.trans_lt hb)
    _ = R := by ring

lemma PlaneWeakGradient.smooth_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt (graphSmooth b f)
      ((InnerProductSpace.toDual ℝ Plane) (∫ y,G (x-y) ∂graphSmoothingMeasure b)) x := by
  have hfi : Integrable f (volume : Measure Plane) := hf.integrable_of_hasCompactSupport hfc
  have he : graphSmooth b f=f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] b.normed volume := by
    rw [graphSmooth_eq_convolution]
    exact real_convolution_comm _ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
    rw [he]
    exact b.hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hfi.locallyIntegrable b.contDiff_normed
  apply (hsm.differentiable (by simp)).differentiableAt.hasFDerivAt.congr_fderiv
  ext v
  rw [he,fderiv_compact_convolution hfi.locallyIntegrable b.contDiff_normed b.hasCompactSupport_normed,
    convolution_mul]
  have hw' := hw v (fun y ↦ b.normed volume (x-y))
    (b.contDiff_normed.comp (contDiff_const.sub contDiff_id))
    (b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x))
    (test_kernel_support hx b hb)
  have hder (y : Plane) : fderiv ℝ (fun z ↦ b.normed volume (x-z)) y v=
      -(fderiv ℝ (b.normed volume) (x-y) v) := by
    have hbn : Differentiable ℝ (b.normed (volume : Measure Plane)) :=
      (b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable (by simp)
    have ht := hbn.differentiableAt.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    have he := ht.fderiv
    dsimp only [Function.comp_def,id_eq] at he
    rw [he]
    simp
  simp_rw [hder,mul_neg,integral_neg,neg_neg] at hw'
  rw [← hw']
  change (∫ y,⟪G y,v⟫*b.normed volume (x-y))=⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫
  have hie : (∫ y,⟪G (x-y),v⟫ ∂graphSmoothingMeasure b)=
      ⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫ := by
    simpa only [real_inner_comm] using
      integral_inner (compact_probability_average_integrable hG hGc b x) v
  rw [← hie]
  rw [graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _),smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y ↦ b.normed volume y*⟪G (x-y),v⟫)
    (volume : Measure Plane) x]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ mul_comm _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.compact_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  have hR : 0<R/2 := Metric.nonempty_ball.mp ⟨x,hx⟩
  have hGu := (InnerProductSpace.toDual ℝ Plane).isometry.uniformContinuous.comp_tendstoUniformly
    (compact_probability_average_uniform hG hGc)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := fun i ↦ graphSmooth (graphMollifier i) f) (g := f)
    (hGu.tendstoUniformlyOnFilter.mono_right le_top)
  · apply Filter.Eventually.prod_mk
      (graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hR))
      (Metric.isOpen_ball.mem_nhds hx) |>.mono
    rintro ⟨i,y⟩ ⟨hi,hy⟩
    exact hw.smooth_hasFDerivAt hf hfc hG hGc (graphMollifier i) hi hy
  · exact Eventually.of_forall fun y ↦ compact_probability_average_uniform hf hfc |>.tendsto_at y

lemma PlaneWeakGradient.continuous_hasFDerivAt {R : ℝ} (hR : 0<R)
    {f : Plane → ℝ} {G : Plane → Plane}
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/4)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → ℝ := fun y ↦ b y*f y
  let G' : Plane → Plane := fun y ↦ b y • G y
  have hf' : Continuous f' := continuous_local_cutoff Metric.isOpen_ball hf b.continuous hbs
  have hG' : Continuous G' := continuous_local_vector_cutoff Metric.isOpen_ball hG b.continuous hbs
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/2)) : b y=1 :=
    b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hw' : PlaneWeakGradient (Metric.ball 0 (R/2)) f' G' :=
    (hw.mono (Metric.ball_subset_ball (by linarith))).local_congr measurableSet_ball
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [f',he y hy])
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [G',he y hy])
  have hx' : x∈Metric.ball (0 : Plane) ((R/2)/2) := by
    have he : (R/2)/2=R/4 := by ring
    rwa [he]
  have hh := hw'.compact_hasFDerivAt hf' b.hasCompactSupport.mul_right hG'
    b.hasCompactSupport.smul_right hx'
  have hx2 : x∈Metric.ball (0 : Plane) (R/2) :=
    (Metric.ball_subset_ball (by linarith : R/4≤R/2)) hx
  have hloc : f'=ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx2] with y hy
    simp [f',he y hy]
  have heG : G' x=G x := by simp [G',he x hx2]
  rw [heG] at hh
  exact hh.congr_of_eventuallyEq hloc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradient.holder_C1 {R L α : ℝ} (hR : 0<R) {f : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (G x) (G y)≤L*(dist x y)^α) :
    ContDiffOn ℝ 1 f (Metric.ball 0 (R/4)) ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ y∈Metric.ball (0 : Plane) (R/4),
        dist (fderiv ℝ f x) (fderiv ℝ f y)≤L*(dist x y)^α := by
  have hd : ∀ x∈Metric.ball (0 : Plane) (R/4),
      HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x :=
    fun x hx ↦ hw.continuous_hasFDerivAt hR hf hG hx
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  constructor
  · rw [show (1 : WithTop ℕ∞)=0+1 by rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    apply ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn (hG.mono hsub)).congr
    intro x hx
    exact (hd x hx).fderiv
  · intro x hx y hy
    rw [(hd x hx).fderiv,(hd y hy).fderiv,(InnerProductSpace.toDual ℝ Plane).isometry.dist_eq]
    exact hHolder x (hsub hx) y (hsub hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

lemma LinearCMCEquation.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane} {U : Set Plane}
    (hU : IsOpen U) (hw : LinearCMCEquation g p B U)
    (hg : EqOn g' g U) (hp : EqOn p' p U) (hB : EqOn B' B U) : LinearCMCEquation g' p' B' U := by
  intro ψ hψ hc hs
  rw [← hw ψ hψ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    by_cases hy : y∈U
    · have he : g'=ᶠ[𝓝 y]g := by
        filter_upwards [hU.mem_nhds hy] with z hz
        exact hg hz
      have hG : gradient g' y=gradient g y := congrArg
        (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) he.fderiv_eq
      rw [hG,hp hy,hB hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hs h))]; rfl

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

lemma LinearCMCEquationNear.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane}
    (hw : LinearCMCEquationNear g p B)
    (hg : g'=ᶠ[𝓝 0]g) (hp : p'=ᶠ[𝓝 0]p) (hB : B'=ᶠ[𝓝 0]B) : LinearCMCEquationNear g' p' B' := by
  obtain ⟨R,hR,hw⟩ := hw
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (hg.and (hp.and hB))
  refine ⟨min r R,lt_min hr hR,?_⟩
  have hsub : Metric.ball (0 : Plane) (min r R)⊆Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  exact (hw.mono (Metric.ball_subset_ball (min_le_right _ _))).congr Metric.isOpen_ball
    (fun _ hy ↦ (he (hsub hy)).1) (fun _ hy ↦ (he (hsub hy)).2.1) (fun _ hy ↦ (he (hsub hy)).2.2)

end CubicTorus

end
end

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

lemma plane_gradient_weight {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (y : Plane) :
    gradient (fun z ↦ cmcWeight (p z)) y=
      (cmcWeight (p y))⁻¹ •
        (p y 0 • gradient (fun z ↦ p z 0) y+p y 1 • gradient (fun z ↦ p z 1) y) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have he := ((cmcWeight_hasFDerivAt (p y)).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)).fderiv
  change fderiv ℝ (fun z ↦ cmcWeight (p z)) y=_ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,inner_gradient_left,
    plane_component_fderiv (hp.of_le (by simp)),plane_inner_components]

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

lemma plane_shape_trace_identity (p : Plane) (L : Plane →L[ℝ] Plane)
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫) :
    (⟪L (EuclideanSpace.single 0 1),cmcJacobian p (L (EuclideanSpace.single 0 1))⟫+
      ⟪L (EuclideanSpace.single 1 1),cmcJacobian p (L (EuclideanSpace.single 1 1))⟫-
      ⟪(cmcWeight p)⁻¹ • L p,cmcJacobian p ((cmcWeight p)⁻¹ • L p)⟫)/cmcWeight p=
      planeTraceSquare ((cmcJacobian p).comp L) := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  have he : L p=p 0 • L (EuclideanSpace.single 0 1)+p 1 • L (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose p]
    simp only [map_add,map_smul]
  simp only [planeTraceSquare,ContinuousLinearMap.comp_apply,cmcJacobian_apply,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,he,inner_add_left,inner_add_right,
    plane_inner_components,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,hc]
  field_simp
  ring

lemma graphSquaredSecondFundamentalForm_formula {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    graphSquaredSecondFundamentalForm g y=
      (⟪gradient (fun z ↦ gradient g z 0) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 0) y)⟫+
        ⟪gradient (fun z ↦ gradient g z 1) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 1) y)⟫-
        ⟪gradient (fun z ↦ cmcWeight (gradient g z)) y,
          cmcJacobian (gradient g y) (gradient (fun z ↦ cmcWeight (gradient g z)) y)⟫)/cmcWeight (gradient g y) := by
  have hi (i : Fin 2) : gradient (fun z ↦ gradient g z i) y=
      fderiv ℝ (gradient g) y (EuclideanSpace.single i 1) := by
    simp_rw [plane_gradient_component]
    exact (plane_hessian_direction hg y _).symm
  have hq : gradient (fun z ↦ cmcWeight (gradient g z)) y=
      (cmcWeight (gradient g y))⁻¹ • fderiv ℝ (gradient g) y (gradient g y) := by
    rw [plane_gradient_weight (plane_gradient_contDiff hg),hi 0,hi 1]
    congr 1
    conv_rhs => rw [plane_decompose (gradient g y)]
    simp only [map_add,map_smul]
  rw [hi 0,hi 1,hq]
  exact (plane_shape_trace_identity (gradient g y) (fderiv ℝ (gradient g) y)
    (plane_hessian_symmetric hg y)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose_sum (v : Plane) : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
  rw [Fin.sum_univ_two]
  exact plane_decompose v

lemma plane_cover_clm_component (L : Plane →L[ℝ] Cover) (v : Plane) (i : Fin 3) :
    L v i=∑ j : Fin 2,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [plane_decompose_sum v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma cover_plane_clm_component (L : Cover →L[ℝ] Plane) (v : Cover) (i : Fin 2) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Plane →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma rectangular_trace (L : Plane →L[ℝ] Cover) (P : Cover →L[ℝ] Plane) :
    coverTrace (L.comp P)=planeTrace (P.comp L) := by
  simp only [coverTrace,planeTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [plane_cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_plane_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma planeTrace_square (L : Plane →L[ℝ] Plane) :
    planeTrace (L.comp L)=planeTraceSquare L := by
  simp only [planeTrace,Fin.sum_univ_two,ContinuousLinearMap.comp_apply]
  rw [plane_decompose (L (EuclideanSpace.single 0 1)),
    plane_decompose (L (EuclideanSpace.single 1 1))]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  unfold planeTraceSquare
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

theorem graph_weingarten {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    fderiv ℝ (fun z ↦ graphSlopeNormal n (gradient g z)) y v=
      -fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v) := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  have hp := plane_gradient_contDiff hg
  have hq := (cmcWeight_hasFDerivAt p).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)
  have hi := (hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt y hq
  have hN := (hasFDerivAt_const n y).sub
    ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt.comp y
      ((hp.differentiable (by simp) y).hasFDerivAt))
  have hd := (hi.smul hN).fderiv
  have he : (fun z ↦ graphSlopeNormal n (gradient g z))=
      (fun z ↦ (cmcWeight (gradient g z))⁻¹ • (n-normalPlaneEmbedding n (gradient g z))) :=
    funext fun z ↦ graphSlopeNormal_weight hn _
  rw [he]
  change fderiv ℝ (fun z ↦ (cmcWeight (gradient g z))⁻¹ •
    (n-normalPlaneEmbedding n (gradient g z))) y=_ at hd
  rw [hd,normalGraph_fderiv_apply hg]
  change _= -(normalPlaneEmbedding n (cmcJacobian p (L v))+⟪p,cmcJacobian p (L v)⟫ • n)
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  have hE : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  rw [hE]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul,
    Function.comp_def, Pi.sub_apply, p, L, map_sub, map_smul, smul_sub,
    zero_sub, smul_neg, neg_add_rev, ← inv_pow]
  module

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

lemma normalGraph_projection_differential {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    (normalPlaneCoordinates n).comp (fderiv ℝ (normalGraph n g) y)=
      ContinuousLinearMap.id ℝ Plane := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply,normalGraph_fderiv_apply hg,map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]
  rfl

lemma graphUnitNormalExtension_fderiv (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    fderiv ℝ (graphUnitNormalExtension a n g) x=
      -((fderiv ℝ (normalGraph n g) (normalPlaneCoordinates n (x-a))).comp
        ((graphShapeOperator g (normalPlaneCoordinates n (x-a))).comp
          (normalPlaneCoordinates n))) := by
  have hN : Differentiable ℝ (fun y ↦ graphSlopeNormal n (gradient g y)) :=
    ((graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)).differentiable (by simp)
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a)
  have hd := ((hN _).hasFDerivAt.comp x hp).fderiv
  change fderiv ℝ (graphUnitNormalExtension a n g) x=_ at hd
  rw [hd]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,neg_apply]
  exact graph_weingarten hn hg _ _

theorem graphUnitNormalExtension_curvature (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    coverTrace ((fderiv ℝ (graphUnitNormalExtension a n g) x).comp
      (fderiv ℝ (graphUnitNormalExtension a n g) x))=
        graphSquaredSecondFundamentalForm g (normalPlaneCoordinates n (x-a)) := by
  let y := normalPlaneCoordinates n (x-a)
  let J := fderiv ℝ (normalGraph n g) y
  let S := graphShapeOperator g y
  let P := normalPlaneCoordinates n
  have hPJ : P.comp J=ContinuousLinearMap.id ℝ Plane := normalGraph_projection_differential hn hg y
  rw [graphUnitNormalExtension_fderiv a hn hg]
  change coverTrace ((-(J.comp (S.comp P))).comp (-(J.comp (S.comp P))))=planeTraceSquare S
  have he : ((-(J.comp (S.comp P))).comp (-(J.comp (S.comp P))))=
      J.comp ((S.comp S).comp P) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : Plane →L[ℝ] Plane ↦ L (S (P v))) hPJ
    simp only [ContinuousLinearMap.comp_apply,neg_apply,map_neg,neg_neg,
      ContinuousLinearMap.id_apply] at h ⊢
    rw [h]
  rw [he,rectangular_trace,ContinuousLinearMap.comp_assoc,hPJ,
    ContinuousLinearMap.comp_id,planeTrace_square]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
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

lemma smooth_unit_normal_derivative {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hu : ∀ᶠ y in 𝓝 x, ‖N y‖=1) :
    (fderiv ℝ N x).adjoint (N x)=0 := by
  have he : (fun y ↦ ⟪N y,N y⟫)=ᶠ[𝓝 x](fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hu] with y hy
    rw [real_inner_self_eq_norm_sq,hy,one_pow]
  have hh := (hN.hasFDerivAt.inner ℝ hN.hasFDerivAt).fderiv
  have hz := he.fderiv_eq (𝕜 := ℝ)
  rw [hh] at hz
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : Cover →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,fderiv_const_apply,zero_apply] at hv
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  rw [real_inner_comm (fderiv ℝ N x v) (N x)] at hv
  nlinarith [real_inner_comm (N x) (fderiv ℝ N x v)]

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

theorem plane_weight_harmonic_potential {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (y : Plane)
    (hz : ∀ i : Fin 2,planeDivergence (fun z ↦ A z (gradient (fun w ↦ p w i) z)) y=0) :
    planeDivergence (fun z ↦ A z (gradient (fun w ↦ cmcWeight (p w)) z)) y=
      (⟪gradient (fun w ↦ p w 0) y,A y (gradient (fun w ↦ p w 0) y)⟫+
        ⟪gradient (fun w ↦ p w 1) y,A y (gradient (fun w ↦ p w 1) y)⟫-
        ⟪gradient (fun w ↦ cmcWeight (p w)) y,A y (gradient (fun w ↦ cmcWeight (p w)) y)⟫)/
        cmcWeight (p y) := by
  let q : Plane → ℝ := fun z ↦ cmcWeight (p z)
  let u : Fin 2 → Plane → ℝ := fun i z ↦ p z i
  let F : Fin 2 → Plane → Plane := fun i z ↦ A z (gradient (u i) z)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp hp
  have hu (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (u i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hp
  have hF (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (F i) := hA.clm_apply (plane_gradient_contDiff (hu i))
  have hquot (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ u i z/q z) :=
    (hu i).div hq (fun z ↦ (cmcWeight_pos _).ne')
  have hprod (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (u i z/q z) • F i z) :=
    (hquot i).smul (hF i)
  have hfield : (fun z ↦ A z (gradient q z))=
      (fun z ↦ (u 0 z/q z) • F 0 z+(u 1 z/q z) • F 1 z) := by
    funext z
    rw [plane_gradient_weight hp]
    simp only [F,u,q,map_smul,map_add,smul_add,smul_smul,div_eq_mul_inv]
    congr 1 <;> congr 1 <;> ring
  change planeDivergence (fun z ↦ A z (gradient q z)) y=_
  rw [hfield,planeDivergence_add
    ((hprod 0).differentiable (by simp) y)
    ((hprod 1).differentiable (by simp) y),
    planeDivergence_smul ((hquot 0).differentiable (by simp) y) ((hF 0).differentiable (by simp) y),
    planeDivergence_smul ((hquot 1).differentiable (by simp) y) ((hF 1).differentiable (by simp) y)]
  have hz' (i : Fin 2) : planeDivergence (F i) y=0 := hz i
  rw [hz' 0,hz' 1,mul_zero,mul_zero,zero_add,zero_add,
    plane_gradient_div ((hu 0).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne',
    plane_gradient_div ((hu 1).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne']
  have he := congrArg (fun v : Plane ↦ ⟪gradient q y,A y v⟫) (plane_gradient_weight hp y)
  change ⟪gradient q y,A y (gradient q y)⟫=_ at he
  simp only [map_smul,map_add,inner_smul_right,inner_add_right] at he
  change _=(⟪gradient (u 0) y,F 0 y⟫+⟪gradient (u 1) y,F 1 y⟫-
    ⟪gradient q y,A y (gradient q y)⟫)/q y
  rw [he]
  simp only [inner_sub_left,real_inner_smul_left]
  dsimp only [F,u,q]
  field_simp [(cmcWeight_pos (p y)).ne']
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmc_graph_curvature_potential {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hU : IsOpen U)
    (hw : ∀ i : Fin 2,LinearCMCEquation
      (fun y ↦ fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ ↦ 0) U)
    {y : Plane} (hy : y∈U) :
    planeDivergence (fun z ↦ cmcJacobian (gradient g z)
      (gradient (fun w ↦ cmcWeight (gradient g w)) z)) y=
        graphSquaredSecondFundamentalForm g y := by
  rw [graphSquaredSecondFundamentalForm_formula hg]
  apply plane_weight_harmonic_potential (plane_gradient_contDiff hg)
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
  intro i
  simp_rw [plane_gradient_component]
  exact (hw i).classical_zero hg
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const) hU y hy

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_trace_square_invariance {n : Cover} (hn : ‖n‖=1)
    {D B : Cover →L[ℝ] Cover}
    (hD : ∀ v,⟪n,D v⟫=0) (hB : ∀ v,⟪n,B v⟫=0)
    (ht : ∀ v,⟪n,v⟫=0 → D v=B v) :
    coverTrace (D.comp D)=coverTrace (B.comp B) := by
  let w := D n-B n
  let R : Cover →L[ℝ] Cover := (innerSL ℝ n).smulRight w
  have hw : ⟪n,w⟫=0 := by rw [inner_sub_right,hD,hB,sub_self]
  have he : D=B+R := by
    apply ContinuousLinearMap.ext
    intro v
    have htv : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
    change D v=B v+⟪n,v⟫ • (D n-B n)
    calc
      D v=D (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [map_sub,map_smul]; module
      _=B (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [ht _ htv]
      _=_ := by rw [map_sub,map_smul]; module
  have hBR : B.comp R=(innerSL ℝ n).smulRight (B w) := by
    apply ContinuousLinearMap.ext
    intro v
    exact map_smul B _ _
  have hRR : R.comp R=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change ⟪n,⟪n,v⟫ • w⟫ • w=0
    rw [real_inner_smul_right,hw,mul_zero,zero_smul]
  have hbr : coverTrace (B.comp R)=0 := by rw [hBR,coverTrace_smulRight]; exact hB w
  have hrb : coverTrace (R.comp B)=0 := by rw [coverTrace_comp_comm,hbr]
  rw [he,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add,coverTrace_add,coverTrace_add,coverTrace_add,hbr,hrb,hRR,
    coverTrace_zero,add_zero,zero_add,add_zero]

theorem graph_normal_extension_curvature (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hu : ∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    (hmatch : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z)) :
    coverTrace ((fderiv ℝ N (a+normalGraph n g y)).comp
      (fderiv ℝ N (a+normalGraph n g y)))=graphSquaredSecondFundamentalForm g y := by
  let x := a+normalGraph n g y
  let K : Cover → Cover := fun v ↦ σ • graphUnitNormalExtension a n g v
  have hK : ContDiff ℝ (⊤ : ℕ∞) K :=
    (graphUnitNormalExtension_contDiff a hn hg).const_smul σ
  have hKu (v : Cover) : ‖K v‖=1 := by
    rcases hσ with rfl|rfl
    · simpa only [K,one_smul] using graphUnitNormalExtension_unit a hn g v
    · simpa only [K,neg_one_smul,norm_neg] using graphUnitNormalExtension_unit a hn g v
  have hm : (fun z ↦ N (a+normalGraph n g z))=ᶠ[𝓝 y](fun z ↦ K (a+normalGraph n g z)) := by
    filter_upwards [hmatch] with z hz
    simpa only [K,graphUnitNormalExtension_graph a hn g g z] using hz
  have hNx : N x=K x := hm.eq_of_nhds
  have hdN := smooth_unit_normal_derivative (hN.differentiable (by simp) x) hu
  have hdK := smooth_unit_normal_derivative (hK.differentiable (by simp) x)
    (Filter.Eventually.of_forall hKu)
  have hnD (v : Cover) : ⟪N x,fderiv ℝ N x v⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hdN,inner_zero_left]
  have hnB (v : Cover) : ⟪N x,fderiv ℝ K x v⟫=0 := by
    rw [hNx,← ContinuousLinearMap.adjoint_inner_left,hdK,inner_zero_left]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have hdmatch := hm.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (N ∘ fun z ↦ a+normalGraph n g z) y=
    fderiv ℝ (K ∘ fun z ↦ a+normalGraph n g z) y at hdmatch
  rw [((hN.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv,
    ((hK.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv] at hdmatch
  have ht (v : Cover) (hv : ⟪N x,v⟫=0) : fderiv ℝ N x v=fderiv ℝ K x v := by
    have hv' : ⟪graphSlopeNormal n (gradient g y),v⟫=0 := by
      rw [hNx] at hv
      change ⟪σ • graphUnitNormalExtension a n g x,v⟫=0 at hv
      rw [graphUnitNormalExtension_graph a hn g g y,real_inner_smul_left] at hv
      rcases hσ with rfl|rfl <;> simpa using hv
    let q := graphInverseMetric (gradient g y)
      (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
    have hvq : fderiv ℝ (normalGraph n g) y q=v := by
      rw [normalGraph_fderiv_apply hg]
      rw [graph_metric_projection hn,hv',zero_smul,sub_zero]
    have he := congrArg (fun L : Plane →L[ℝ] Cover ↦ L q) hdmatch
    simp only [ContinuousLinearMap.comp_apply] at he
    rw [← hvq]
    exact he
  rw [normal_trace_square_invariance (hu.self_of_nhds) hnD hnB ht]
  have hpot : coverTrace ((fderiv ℝ K x).comp (fderiv ℝ K x))=
      coverTrace ((fderiv ℝ (graphUnitNormalExtension a n g) x).comp
        (fderiv ℝ (graphUnitNormalExtension a n g) x)) := by
    rcases hσ with rfl|rfl
    · simp only [K,one_smul]
    · simp only [K,neg_one_smul]
      change coverTrace ((fderiv ℝ (-graphUnitNormalExtension a n g) x).comp
        (fderiv ℝ (-graphUnitNormalExtension a n g) x))=_
      rw [fderiv_neg,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,neg_neg]
  rw [hpot,graphUnitNormalExtension_curvature a hn hg]
  simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]

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

lemma surfaceJacobiB_continuous (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Continuous (fun p : SurfaceJet μ × SurfaceJet μ ↦ surfaceJacobiB μ q p.1 p.2) := by
  unfold surfaceJacobiB
  fun_prop

end CubicTorus

end
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

theorem cutoff_graph_patch_continuous_mass {A O U : Set Cover} (hA : MeasurableSet A)
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
    (f : BoundedContinuousFunction Cover ℝ) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let f₀ : Cover → ℝ := fun x => f x / M
  have hfc : Continuous f₀ := f.continuous.div_const M
  have hfb (x : Cover) : |f₀ x| ≤ 1 := by
    rw [show f₀ x = f x / M from rfl, abs_div, abs_of_pos hM]
    apply (div_le_one hM).mpr
    exact (f.norm_coe_le_norm x).trans (by dsimp [M]; linarith)
  have he := cutoff_graph_patch_limit_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb
    (fun i => smoothApprox_contDiff hfc.measurable hfb i)
    (fun i x => smoothApprox_bound hfb i x)
    (fun x _ => ContDiffBump.convolution_tendsto_right_of_continuous
      mollifier_rOut_tendsto hfc x)
  have he' := congrArg (fun t : ℝ => M * t) he
  rw [← integral_const_mul, ← integral_const_mul] at he'
  convert he' using 1 <;> congr 1 <;> funext x <;> dsimp only [f₀] <;> field_simp [ne_of_gt hM]

theorem cutoff_graph_patch_measure {A O U : Set Cover} (hA : MeasurableSet A)
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
    Measure.map Prod.fst
      (((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}).withDensity
        (fun z => ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane => a + normalGraph n g y)
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hI : Integrable (fun z : BlowupNormalBundle => φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hG := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy => (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hGc := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy => (graphAreaVector_continuousAt n (hc y hy)).norm)
  let := isFiniteMeasure_withDensity_ofReal hI.hasFiniteIntegral
  let := isFiniteMeasure_withDensity_ofReal hG.hasFiniteIntegral
  have hchart : Continuous (fun y : Plane => a + normalGraph n g y) := by
    simpa only [id_eq] using graph_trace_continuous a n hg.continuous continuous_id
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_fst f.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable
      hchart.measurable
      f.continuous.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun z : BlowupNormalBundle => ENNReal.ofReal (φ z.1))
      (hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal
      (ae_of_all μ fun _ => ENNReal.ofReal_lt_top) _,
    integral_withDensity_eq_integral_toReal_smul hGc.measurable.ennreal_ofReal
      (ae_of_all volume fun _ => ENNReal.ofReal_lt_top) _]
  simp_rw [ENNReal.toReal_ofReal (hφb _).1, smul_eq_mul,
    ENNReal.toReal_ofReal (mul_nonneg (hφb _).1 (norm_nonneg _))]
  convert cutoff_graph_patch_continuous_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weighted_bundle_section {μ : Measure BlowupNormalBundle} {φ : Cover → ℝ}
    (hφ : Measurable φ) {s : Cover → BlowupNormalBundle} (hs : Measurable s)
    (hae : ∀ᵐ z ∂μ, 0 < φ z.1 → s z.1 = z) :
    μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map s (Measure.map Prod.fst (μ.withDensity (fun z => ENNReal.ofReal (φ z.1)))) := by
  rw [Measure.map_map hs measurable_fst]
  symm
  calc
    _ = Measure.map id (μ.withDensity (fun z => ENNReal.ofReal (φ z.1))) := by
      apply Measure.map_congr
      apply (ae_withDensity_iff (hφ.comp measurable_fst).ennreal_ofReal).mpr
      filter_upwards [hae] with z hz hpos
      exact hz (ENNReal.ofReal_ne_zero_iff.mp hpos)
    _ = _ := Measure.map_id

theorem cutoff_graph_patch_bundle_measure {A O U : Set Cover} (hA : MeasurableSet A)
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
    (((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}).withDensity
      (fun z => ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane => graphNormalSection a hn g (a + normalGraph n g y))
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  have ha := cutoff_graph_patch_normal_ae hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb
  have hs := weighted_bundle_section hφ.continuous.measurable
    (graphNormalSection_measurable a hn g) (show ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → graphNormalSection a hn g z.1 = z from by
        filter_upwards [ha] with z hz hpos
        refine Prod.ext ?_ ?_
        · rfl
        · exact Subtype.ext (hz hpos).symm)
  rw [hs, cutoff_graph_patch_measure hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb]
  have hchart : Measurable (fun y : Plane => a + normalGraph n g y) := by
    simpa only [id_eq] using (graph_trace_continuous a n hg.continuous continuous_id).measurable
  exact Measure.map_map (graphNormalSection_measurable a hn g) hchart

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma clampCell_coe (x : CompactCell) : clampCell (x : Cover) = x := by
  apply Subtype.ext
  ext i
  change max 0 (min 1 ((x : Cover) i)) = (x : Cover) i
  rw [min_eq_right (compactCell_coordinates x i).2,
    max_eq_right (compactCell_coordinates x i).1]

lemma normalCellProjection_cover (z : NormalBundle) :
    normalCellProjection (normalCoverMap z) = z := by
  change (clampCell (z.1 : Cover), z.2) = z
  rw [clampCell_coe]

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (Measure.map f μ).withDensity w = Measure.map f (μ.withDensity (w ∘ f)) := by
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, Measure.map_apply hf hs,
    withDensity_apply _ (hs.preimage hf), setLIntegral_map hs hw hf]
  rfl

lemma withDensity_restrict_of_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ≥0∞} {S : Set α} (hS : MeasurableSet S)
    (hs : ∀ x, x ∉ S → w x = 0) :
    (μ.restrict S).withDensity w = μ.withDensity w := by
  rw [← withDensity_indicator hS]
  congr 1
  apply Set.indicator_eq_self.2
  intro x hx
  by_contra hn
  exact hx (hs x hn)

theorem normalMeasure_graph_area_measure {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U →
      (quotientMap x ∈ E ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
    Measure.map (actualNormalGraphChart a hn g)
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let O : Set Cover := {x | ∀ i, 0 < x i ∧ x i < 1}
  have hmO : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} := by
    change MeasurableSet {z : BlowupNormalBundle | ∀ i, 0 < z.1 i ∧ z.1 i < 1}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun z : BlowupNormalBundle => z.1 i) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hf (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (_hb : ∀ x, ‖F x‖ ≤ 1) :=
    normalCoverMeasure_local_flux hE hμ hF hs hO
  have he := cutoff_graph_patch_bundle_measure (hE.preimage measurable_quotientMap)
    a hn hg hc hgraph (normalMeasure_cutoff_saturation hμ O) hf
    hφ hsφ hφU hφO hφR hφb
  rw [withDensity_restrict_of_support hmO (fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h)), ENNReal.ofReal_zero])] at he
  have hcmap : (normalCoverMeasure μ : Measure BlowupNormalBundle) =
      Measure.map normalCoverMap (μ : Measure NormalBundle) := FiniteMeasure.toMeasure_map μ normalCoverMap
  rw [hcmap, map_withDensity_comp _ continuous_normalCoverMap.measurable
    (w := fun z : BlowupNormalBundle => ENNReal.ofReal (φ z.1))
    ((hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal)] at he
  have hp := congrArg (Measure.map normalCellProjection) he
  rw [Measure.map_map continuous_normalCellProjection.measurable continuous_normalCoverMap.measurable] at hp
  have hid : normalCellProjection ∘ normalCoverMap = id := funext normalCellProjection_cover
  rw [hid, Measure.map_id] at hp
  have hchart : Measurable (fun y : Plane => graphNormalSection a hn g (a+normalGraph n g y)) := by
    apply (graphNormalSection_measurable a hn g).comp
    simpa only [id_eq] using (graph_trace_continuous a n hg.continuous continuous_id).measurable
  rw [Measure.map_map continuous_normalCellProjection.measurable hchart] at hp
  exact hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lpPullbackLE_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) (u : Lp F 2 μ) :
    lpPullbackLE hf hle u =ᵐ[ν] u ∘ f := by
  have hmp : MeasurePreserving f ν (Measure.map f ν) := ⟨hf,rfl⟩
  have hr := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1)
    (by simp : (1 : ℝ≥0∞) ≠ ∞) (by simpa using hle) u
  exact (Lp.coeFn_compMeasurePreserving _ hmp).trans (hmp.quasiMeasurePreserving.ae_eq_comp hr)

lemma lpPullbackLE_congr_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) {u v : β → F}
    (huv : u =ᵐ[μ] v) : u ∘ f =ᵐ[ν] v ∘ f := by
  exact (show Measure.QuasiMeasurePreserving f ν μ from
    ⟨hf,Measure.absolutelyContinuous_of_le hle⟩).ae_eq_comp huv

lemma graphAreaVector_norm_ge_one {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : 1 ≤ ‖graphAreaVector n g y‖ := by
  have hs := graphAreaVector_norm_sq hn g y
  nlinarith [norm_nonneg (graphAreaVector n g y), sq_nonneg ‖gradient g y‖]

lemma graph_chart_measure_le {μ : Measure NormalBundle}
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ}
    (hg : Continuous g) {φ : Cover → ℝ} (hφ : ∀ x, φ x ∈ Icc 0 1)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {S : Set Plane} (hS : MeasurableSet S)
    (hunit : ∀ y ∈ S, φ (a+normalGraph n g y)=1) :
    Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤ μ := by
  have hd : volume.restrict S ≤ volume.withDensity (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    rw [← withDensity_indicator_one hS]
    apply withDensity_mono
    filter_upwards [] with y
    by_cases hy : y∈S
    · simp only [Set.indicator_of_mem hy, Pi.one_apply, hunit y hy, one_mul]
      simpa using ENNReal.ofReal_le_ofReal (graphAreaVector_norm_ge_one hn g y)
    · simp [hy]
  have hcut : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) ≤ μ := by
    conv_rhs => rw [← withDensity_one (μ := μ)]
    apply withDensity_mono
    exact ae_of_all _ (fun z => by simpa using ENNReal.ofReal_le_ofReal (hφ z.1).2)
  exact ((Measure.map_mono hd (actualNormalGraphChart_measurable a hn hg)).trans_eq hm.symm).trans hcut

lemma graphCovector_apply (n : Cover) (g : Plane → ℝ) (y : Plane) (v : Cover) :
    graphCovector n g y v = normalPlaneCoordinates n v + ⟪n,v⟫ • gradient g y := rfl

lemma graphCovectorLp_ae {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (u : Lp Cover 2 ν) :
    graphCovectorLp hn hg u =ᵐ[ν] fun y => graphCovector n g y (u y) := by
  have ha := (graphCovector_memLp (ν := ν) hn hg).coeFn_toLp
  have hb := (ContinuousLinearMap.id ℝ (Cover →L[ℝ] Plane)).coeFn_holder
    ((graphCovector_memLp (ν := ν) hn hg).toLp (graphCovector n g)) u (r := 2)
  filter_upwards [ha,hb] with y ha hb
  change (graphCovectorLp hn hg u) y = _ at hb
  simpa only [ContinuousLinearMap.id_apply,ha] using hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_duality {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ)
    (y v : Plane) (w : Cover) :
    ⟪graphCovector n g y w,v⟫ =
      ⟪w,normalPlaneEmbedding n v+⟪gradient g y,v⟫ • n⟫ := by
  rw [graphCovector_apply,inner_add_left,real_inner_smul_left,
    inner_add_right,inner_smul_right]
  have he : ⟪normalPlaneCoordinates n w,v⟫=⟪w,normalPlaneEmbedding n v⟫ := by
    calc
      _ = ⟪v,normalPlaneCoordinates n w⟫ := real_inner_comm _ _
      _ = ⟪normalPlaneEmbedding n v,w⟫ := (normalPlaneEmbedding_inner_coordinates hn v w).symm
      _ = _ := real_inner_comm _ _
  rw [he]
  have hi : ⟪n,w⟫=⟪w,n⟫ := real_inner_comm _ _
  rw [hi]
  ring

lemma graphCovector_normal_zero {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    graphCovector n g y (graphSlopeNormal n (gradient g y))=0 := by
  rw [graphSlopeNormal_weight hn,map_smul,map_sub,graphCovector_apply,
    graphCovector_apply,normalPlaneCoordinates_normal hn,
    normalPlaneCoordinates_embedding,real_inner_self_eq_norm_sq,hn,one_pow,
    normalPlaneEmbedding_inner hn,one_smul,zero_smul,zero_add,add_zero,sub_self,smul_zero]

lemma gradient_graph_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {y : Plane} (hg : DifferentiableAt ℝ g y)
    {f : Cover → ℝ} (hf : DifferentiableAt ℝ f (a+normalGraph n g y)) :
    gradient (fun z => f (a+normalGraph n g z)) y =
      graphCovector n g y (gradient f (a+normalGraph n g y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,graphCovector_duality hn]
  have hc := hf.hasFDerivAt.comp y ((normalGraph_hasFDerivAt hg).const_add a)
  change (fderiv ℝ (f ∘ fun x => a+normalGraph n g x) y) v = _
  rw [hc.fderiv,ContinuousLinearMap.comp_apply,← inner_gradient_left]
  congr 1
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    inner_gradient_left]
  rfl

lemma actualNormalGraphChart_position (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {y : Plane}
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    ((actualNormalGraphChart a hn g y).1 : Cover)=a+normalGraph n g y := by
  change ((clampCell (a+normalGraph n g y)) : Cover)=_
  ext i
  change max 0 (min 1 ((a+normalGraph n g y) i))=(a+normalGraph n g y) i
  rw [min_eq_right (hy i).2,max_eq_right (hy i).1]

lemma actualNormalGraphChart_normal (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    ((actualNormalGraphChart a hn g y).2 : Cover)=graphSlopeNormal n (gradient g y) :=
  graphUnitNormalExtension_graph a hn g g y

lemma smoothScalarGradient_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (f : smoothPeriodicScalars) {g : Plane → ℝ} {y : Plane}
    (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    graphCovector n g y (smoothScalarGradient f (actualNormalGraphChart a hn g y))=
      gradient (fun z => f.val (a+normalGraph n g z)) y := by
  change graphCovector n g y (gradient f.val (actualNormalGraphChart a hn g y).1-
    ⟪((actualNormalGraphChart a hn g y).2 : Cover),gradient f.val (actualNormalGraphChart a hn g y).1⟫ •
      ((actualNormalGraphChart a hn g y).2 : Cover))=_
  rw [actualNormalGraphChart_position a hn g hy,actualNormalGraphChart_normal,
    map_sub,map_smul,graphCovector_normal_zero hn,smul_zero,sub_zero]
  exact (gradient_graph_trace a hn hgy (f.property.1.differentiable (by simp) _)).symm

lemma PlaneWeakGradientOn.congr {S : Set Plane} {u u' : Plane → ℝ}
    {G G' : Plane → Plane} (h : PlaneWeakGradientOn S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradientOn S u' G' := by
  intro v ψ hψ hc hs
  have hleft : (∫ y in S, ⟪G' y,v⟫*ψ y)=(∫ y in S, ⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono (fun _ he => by dsimp only; rw [he]))
  have hright : (∫ y in S, u' y*fderiv ℝ ψ y v)=(∫ y in S, u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono (fun _ he => by dsimp only; rw [he]))
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma C1_weak_gradient_on {S : Set Plane} (hS : IsOpen S)
    {f : Plane → ℝ} (hf : Continuous f) (hfc : ContDiffOn ℝ 1 f S) :
    PlaneWeakGradientOn S f (gradient f) := by
  intro v ψ hψ hc hs
  have hi₁ : (∫ y in S, ⟪gradient f y,v⟫*ψ y)=(∫ y, ⟪gradient f y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have hi₂ : (∫ y in S, f y*fderiv ℝ ψ y v)=(∫ y, f y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hy (hs ((tsupport_fderiv_apply_subset (f := ψ) ℝ v) h))),mul_zero]
  rw [hi₁,hi₂]
  simpa only [inner_gradient_left] using C1_local_integration_by_parts hS hf hfc
    (hψ.of_le (by simp)) hc hs v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_pair_scalar_measure {ν : Measure Plane} {u : Lp ℝ 2 ν} {φ : Plane → ℝ}
    (hφ : MemLp φ 2 ν) : ⟪u,hφ.toLp φ⟫=(∫ y,u y*φ y ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_pair_vector_measure {ν : Measure Plane} {G : Lp Plane 2 ν}
    {f : Plane → Plane} (hf : MemLp f 2 ν) :
    ⟪G,hf.toLp f⟫=(∫ y,⟪G y,f y⟫ ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

lemma PlaneWeakGradientOn.L2_limit {S : Set Plane}
    {u : ℕ → Lp ℝ 2 (volume.restrict S)}
    {G : ℕ → Lp Plane 2 (volume.restrict S)}
    {u₀ : Lp ℝ 2 (volume.restrict S)} {G₀ : Lp Plane 2 (volume.restrict S)}
    (hu : Tendsto u atTop (𝓝 u₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (hweak : ∀ i,PlaneWeakGradientOn S (u i) (G i)) :
    PlaneWeakGradientOn S u₀ G₀ := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y => ψ y • v
  have ha : MemLp a 2 (volume.restrict S) :=
    ((hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport
      hc.smul_right (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let A := ha.toLp a
  let b : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hb : MemLp b 2 (volume.restrict S) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let B := hb.toLp b
  have hi (W : Lp Plane 2 (volume.restrict S)) :
      ⟪W,A⟫=(∫ y in S,⟪W y,v⟫*ψ y) := by
    rw [L2_pair_vector_measure ha]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [a,inner_smul_right]
    ring
  have he (i : ℕ) : ⟪G i,A⟫= -⟪u i,B⟫ := by
    rw [hi,L2_pair_scalar_measure hb]
    exact hweak i v ψ hψ hc hs
  have hleft := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := B))).neg
  have hh := tendsto_nhds_unique (hleft.congr' (Eventually.of_forall he)) hright
  rw [hi,L2_pair_scalar_measure hb] at hh
  exact hh

lemma graph_trace_contDiffOn_C1 (a n : Cover) {g : Plane → ℝ} {S : Set Plane}
    (hg : ContDiffOn ℝ 1 g S) {f : Cover → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (fun y => f (a+normalGraph n g y)) S := by
  have hgraph : ContDiffOn ℝ 1 (fun y => a+normalGraph n g y) S :=
    contDiffOn_const.add ((normalPlaneLinearIsometry n).contDiff.contDiffOn.add
      (hg.smul contDiffOn_const))
  exact hf.comp_contDiffOn hgraph

lemma surfaceSmoothJet_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) (f : smoothPeriodicScalars) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
        (surfaceSmoothJet μ f).1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
          (surfaceSmoothJet μ f).2)) := by
  let chart := actualNormalGraphChart a hn g
  have hchart : Measurable chart := actualNormalGraphChart_measurable a hn hg.continuous
  have hv := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).1).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hw := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).2).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hv' : lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1 =ᵐ[volume.restrict S]
      (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [hv,ae_restrict_mem hS.measurableSet] with y hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1) y = f.val (chart y).1 at hy
    rw [hy]
    change f.val (actualNormalGraphChart a hn g y).1 = _
    rw [actualNormalGraphChart_position a hn g (hcell y hSy)]
  have hw' : graphCovectorLp hn hg (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2)
      =ᵐ[volume.restrict S] gradient (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [graphCovectorLp_ae hn hg
      (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2),hw,
      ae_restrict_mem hS.measurableSet] with y hmap hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2) y = smoothScalarGradient f (chart y) at hy
    rw [hmap,hy]
    exact smoothScalarGradient_graph_covector a hn f
      (((hgc y hSy).contDiffAt (hS.mem_nhds hSy)).differentiableAt (by simp)) (hcell y hSy)
  exact (C1_weak_gradient_on hS
    (graph_trace_continuous a n hg.continuous f.property.1.continuous)
    (graph_trace_contDiffOn_C1 a n hgc (f.property.1.of_le (by simp)))).congr hv' hw'

theorem surfaceH1_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.2)) := by
  obtain ⟨w,hw,hl⟩ := mem_closure_iff_seq_limit.mp hu
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  apply PlaneWeakGradientOn.L2_limit
    (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_fst.tendsto u).comp hl))
    (((graphCovectorLp hn hg).continuous.tendsto _).comp
      (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_snd.tendsto u).comp hl)))
  intro i
  obtain ⟨f,hf⟩ := hw i
  simp only [Function.comp_apply]
  rw [← hf]
  exact surfaceSmoothJet_chart_weak_gradient μ a hn hg hS hgc hcell hdom f

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Tangency
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

lemma smoothScalarGradient_tangent (f : smoothPeriodicScalars) (z : NormalBundle) :
    ⟪(z.2 : Cover),smoothScalarGradient f z⟫=0 := by
  change ⟪(z.2 : Cover),gradient f.val z.1-
    ⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
  rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,z.2.property]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_metric_pairing {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) (v w : Cover)
    (hw : ⟪graphSlopeNormal n (gradient g y),w⟫=0) :
    ⟪v,w⟫=cmcWeight (gradient g y)*
      ⟪graphCovector n g y v,cmcJacobian (gradient g y) (graphCovector n g y w)⟫ := by
  have hp := graph_metric_projection hn (gradient g y) w
  change normalPlaneEmbedding n (graphInverseMetric (gradient g y) (graphCovector n g y w))+
    ⟪gradient g y,graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ • n = _ at hp
  rw [hw,zero_smul,sub_zero] at hp
  calc
    ⟪v,w⟫ = ⟪graphCovector n g y v,
        graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ := by
      rw [graphCovector_duality hn,hp]
    _ = _ := by rw [graphInverseMetric,smul_apply,inner_smul_right]

lemma graph_area_integral {μ : Measure NormalBundle} (a : Cover) {n : Cover}
    (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {F : NormalBundle → ℝ} (hF : AEStronglyMeasurable F μ) :
    (∫ z,φ z.1*F z ∂μ)=∫ y,φ (a+normalGraph n g y)*‖graphAreaVector n g y‖*
      F (actualNormalGraphChart a hn g y) := by
  have hf : Measurable (fun z : NormalBundle => ENNReal.ofReal (φ z.1)) :=
    (hφ.comp (measurable_subtype_coe.comp measurable_fst)).ennreal_ofReal
  have hG : Measurable (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    have hc : Continuous (fun y => a+normalGraph n g y) :=
      graph_trace_continuous a n hg continuous_id
    have hmgrad : Measurable (gradient g) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have harea : Measurable (fun y => ‖graphAreaVector n g y‖) := by
      exact (measurable_const.sub ((normalPlaneLinearIsometry n).continuous.measurable.comp hmgrad)).norm
    exact ((hφ.comp hc.measurable).mul harea).ennreal_ofReal
  have hFm : AEStronglyMeasurable F (μ.withDensity (fun z => ENNReal.ofReal (φ z.1))) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  have he := congrArg (fun ν : Measure NormalBundle => ∫ z,F z ∂ν) hm
  rw [integral_map (actualNormalGraphChart_measurable a hn hg).aemeasurable
    (by rwa [← hm])] at he
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hG
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at he
  simpa only [ENNReal.toReal_ofReal (hφ0 _),
    ENNReal.toReal_ofReal (mul_nonneg (hφ0 _) (norm_nonneg _)),smul_eq_mul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodicGraphScalar_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)]
      (fun z => χ z*graphHeightExtension a n ψ z) :=
  latticePeriodize_eventuallyEq hc.mul_right
    (tsupport_mul_subset_left.trans hO) (compactCell_coordinates x)

lemma periodicGraphScalar_zero_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell)
    (hx : (x : Cover)∉tsupport χ) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)] (fun _ => 0) := by
  apply (periodicGraphScalar_germ a n hχ hc hO hψ x).trans
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [Pi.zero_apply] at hy
  simp only [hy,zero_mul]

lemma periodicGraphScalar_graph_germ (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    (fun z => (periodicGraphScalar a n hχ hc hψ).val (a+normalGraph n g z))=ᶠ[𝓝 y] ψ := by
  have hpos := actualNormalGraphChart_position a hn g hy
  have he := periodicGraphScalar_germ a n hχ hc hO hψ (actualNormalGraphChart a hn g y).1
  rw [hpos] at he
  have htrace : Continuous (fun z => a+normalGraph n g z) :=
    graph_trace_continuous a n hg continuous_id
  apply (he.comp_tendsto htrace.continuousAt).trans
  have hval (z : Plane) : graphHeightExtension a n ψ (a+normalGraph n g z)=ψ z := by
    rw [graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  by_cases hys : y∈tsupport ψ
  · filter_upwards [hS.mem_nhds (hs hys)] with z hz
    dsimp only [Function.comp_apply]
    rw [hval,hunit z hz,one_mul]
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
    dsimp only [Function.comp_apply]
    simp only [Pi.zero_apply] at hz
    rw [hval,hz,mul_zero]

lemma periodicGraphScalar_graph_value (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) (actualNormalGraphChart a hn g y)=ψ y := by
  change (periodicGraphScalar a n hχ hc hψ).val (actualNormalGraphChart a hn g y).1=ψ y
  rw [actualNormalGraphChart_position a hn g hy]
  exact (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).eq_of_nhds

lemma periodicGraphScalar_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    graphCovector n g y (smoothScalarGradient (periodicGraphScalar a n hχ hc hψ)
      (actualNormalGraphChart a hn g y))=gradient ψ y := by
  rw [smoothScalarGradient_graph_covector a hn _ hgy hy]
  have he := (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).fderiv_eq (𝕜 := ℝ)
  simp only [gradient,he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_smooth_integral (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=
      ∫ z,⟪u.2 z,smoothScalarGradient f z⟫-q z*u.1 z*smoothScalarValue f z ∂(μ : Measure NormalBundle) := by
  unfold surfaceJacobiB
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner u.2 (surfaceSmoothJet μ f).2)
    (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceSmoothJet μ f).1)]
  apply integral_congr_ae
  filter_upwards [(smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_lpSMul (r := 2) q u.1] with z hf hg hq
  change (surfaceSmoothJet μ f).1 z=smoothScalarValue f z at hf
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hg
  change (surfaceMultiplier μ q u.1) z=_ at hq
  simp only [hf,hg,hq,smul_eq_mul,Pi.mul_apply,
    RCLike.inner_apply,RCLike.conj_to_real]
  ring

lemma periodicGraphScalar_zero_jet (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : NormalBundle)
    (hz : (z.1 : Cover)∉tsupport χ) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z=0 ∧
    smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z=0 := by
  have he := periodicGraphScalar_zero_germ a n hχ hc hO hψ z.1 hz
  refine ⟨he.eq_of_nhds,?_⟩
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change gradient (periodicGraphScalar a n hχ hc hψ).val z.1-
    ⟪(z.2 : Cover),gradient (periodicGraphScalar a n hχ hc hψ).val z.1⟫ • (z.2 : Cover)=0
  simp [gradient,hd]

lemma surfaceJacobiB_periodicGraphScalar_weight (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {φ : Cover → ℝ} (hunit : ∀ x∈tsupport χ,φ x=1) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ z,φ z.1*(⟪u.2 z,smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z⟫-
        q z*u.1 z*smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z) ∂(μ : Measure NormalBundle) := by
  rw [surfaceJacobiB_smooth_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : (z.1 : Cover)∈tsupport χ
  · rw [hunit _ hz,one_mul]
  · obtain ⟨hv,hg⟩ := periodicGraphScalar_zero_jet a n hχ hc hO hψ z hz
    simp only [hv,hg,inner_zero_right,mul_zero,sub_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceJacobiB_chart_form (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hφO : tsupport φ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    (hgc : ∀ y,φ (a+normalGraph n g y)≠0 → DifferentiableAt ℝ g y)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y∈S,χ (a+normalGraph n g y)=1)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ⊆S) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)),
          cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*q (actualNormalGraphChart a hn g y)*
          u.1 (actualNormalGraphChart a hn g y)*ψ y := by
  let f := periodicGraphScalar a n hχ hc hψ
  have hF : AEStronglyMeasurable (fun z => ⟪u.2 z,smoothScalarGradient f z⟫-
        q z*u.1 z*smoothScalarValue f z) (μ : Measure NormalBundle) :=
    (Lp.aestronglyMeasurable u.2 |>.inner (smoothScalarGradient f).continuous.aestronglyMeasurable).sub
      (((Lp.aestronglyMeasurable q).mul (Lp.aestronglyMeasurable u.1)).mul
        (smoothScalarValue f).continuous.aestronglyMeasurable)
  rw [surfaceJacobiB_periodicGraphScalar_weight μ q u a n hχ hc hχO hψ hφχ,
    graph_area_integral a hn hg hφ hφ0 hm hF,← integral_indicator hS.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with y
  have hφS {y : Plane} (hy : y∈S) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  by_cases hyφ : φ (a+normalGraph n g y)=0
  · have hyS : y∉S := by intro hy; have := hφS hy; exact zero_ne_one (hyφ.symm.trans this)
    simp only [hyφ,zero_mul,indicator_of_notMem hyS]
  · have hypos : ∀ i,(a+normalGraph n g y) i∈Icc 0 1 := by
      have hx : a+normalGraph n g y∈tsupport φ := subset_tsupport _ hyφ
      exact fun i => ⟨(hφO hx i).1.le,(hφO hx i).2.le⟩
    have hv := periodicGraphScalar_graph_value a hn hχ hc hχO hψ hg hS hunit hs hypos
    have hgrad := periodicGraphScalar_graph_covector a hn hχ hc hχO hψ hg hS hunit hs
      (hgc y hyφ) hypos
    have ht := smoothScalarGradient_tangent f (actualNormalGraphChart a hn g y)
    rw [actualNormalGraphChart_normal] at ht
    rw [graphCovector_metric_pairing hn g y _ _ ht,hgrad,hv,graphAreaVector_norm_sqrt hn]
    change φ (a+normalGraph n g y)*cmcWeight (gradient g y)*
      (cmcWeight (gradient g y)*⟪_,_⟫-_*_*ψ y)=_
    by_cases hyS : y∈S
    · rw [indicator_of_mem hyS,hφS hyS]
      ring
    · have hyψ : y∉tsupport ψ := fun h => hyS (hs h)
      have hgz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hyψ]
      rw [indicator_of_notMem hyS,image_eq_zero_of_notMem_tsupport hyψ,hgz,map_zero,inner_zero_right]
      ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_measure_scalar_test_integrable {ν : Measure Plane} (u : Lp ℝ 2 ν)
    {ψ : Plane → ℝ} (hψ : MemLp ψ 2 ν) : Integrable (fun y => u y*ψ y) ν :=
  (Lp.memLp u).integrable_mul hψ

lemma L2_measure_vector_test_integrable {ν : Measure Plane} (G : Lp Plane 2 ν)
    {F : Plane → Plane} (hF : MemLp F 2 ν) : Integrable (fun y => ⟪G y,F y⟫) ν := by
  apply (L2.integrable_inner (𝕜 := ℝ) G (hF.toLp F)).congr
  filter_upwards [hF.coeFn_toLp] with y hy
  exact congrArg (inner ℝ (G y)) hy

theorem PlaneWeakGradientOn.vector_ibp {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {F : Plane → Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hs : tsupport F⊆S) :
    (∫ y in S,⟪G y,F y⟫)= -(∫ y in S,u y*planeDivergence F y) := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i 1
  let D (i : Fin 2) : Plane → ℝ := fun y => F y i
  have hD (i) : ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hsD (i) : tsupport (D i)⊆tsupport F := by
    apply closure_mono
    intro y hy
    change F y≠0
    intro hz
    apply hy
    change F y i=0
    rw [hz]
    rfl
  have hcD (i) : HasCompactSupport (D i) := hc.of_isClosed_subset (isClosed_tsupport _) (hsD i)
  have hi (i) : Integrable (fun y => G y i*F y i) (volume.restrict S) := by
    exact ((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).comp_memLp G).integrable_mul
      (((hD i).continuous.memLp_of_hasCompactSupport (p := 2) (hcD i)).mono_measure Measure.restrict_le_self)
  have hj (i) : Integrable (fun y => u y*fderiv ℝ (D i) y (e i)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      ((((hD i).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hcD i).fderiv_apply ℝ (e i)) |>.mono_measure Measure.restrict_le_self)
  have he (i) := hw (e i) (D i) (hD i) (hcD i) ((hsD i).trans hs)
  simp only [e,EuclideanSpace.inner_single_right,conj_trivial,one_mul,D] at he
  have hj' (i) : Integrable (fun y => u y*(fderiv ℝ F y (e i)) i) (volume.restrict S) := by
    simpa only [D,plane_component_fderiv (hF.of_le (by simp))] using hj i
  simp_rw [plane_component_fderiv (hF.of_le (by simp))] at he
  simp_rw [plane_inner_components,planeDivergence,mul_add]
  rw [integral_add (hi 0) (hi 1),integral_add (hj' 0) (hj' 1),he 0,he 1]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_hasCompactSupport {F : Plane → Plane}
    (hc : HasCompactSupport F) : HasCompactSupport (planeDivergence F) := by
  apply hc.mono'
  intro y hy
  by_contra hys
  have hz := fderiv_of_notMem_tsupport ℝ hys
  apply hy
  simp [planeDivergence,hz]

theorem PlaneWeakGradientOn.ground_state {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) :
    (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
      q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=
    ∫ y in S,⟪q y • G y+u y • gradient q y,
      A y (gradient (fun z => q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgψ := plane_gradient_contDiff hψ
  let H : Plane → Plane := fun y => A y (gradient q y)
  let F : Plane → Plane := fun y => (q y*ψ y) • H y
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hA.clm_apply hgq
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hq.mul hψ).smul hH
  have hcF : HasCompactSupport F := hc.mul_left.smul_right
  have hsF : tsupport F⊆S :=
    (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_right.trans hs)
  have hibp := hw.vector_ibp hF hcF hsF
  have hiF : Integrable (fun y => ⟪G y,F y⟫) (volume.restrict S) :=
    L2_measure_vector_test_integrable G
      ((hF.continuous.memLp_of_hasCompactSupport hcF).mono_measure Measure.restrict_le_self)
  have hiD : Integrable (fun y => u y*planeDivergence F y) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((planeDivergence_continuous (hF.of_le (by simp))).memLp_of_hasCompactSupport
        (planeDivergence_hasCompactSupport hcF)).mono_measure Measure.restrict_le_self)
  let V : Plane → Plane := fun y => (q y)^2 • A y (gradient ψ y)
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := (hq.pow 2).smul (hA.clm_apply hgψ)
  have hcV : HasCompactSupport V := by
    apply hc.mono'
    intro y hy
    by_contra hys
    have hz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hys]
    apply hy
    simp [V,hz]
  have hiV : Integrable (fun y => (q y)^2*⟪G y,A y (gradient ψ y)⟫)
      (volume.restrict S) := by
    simpa only [V,real_inner_smul_right] using L2_measure_vector_test_integrable G
      ((hV.continuous.memLp_of_hasCompactSupport hcV).mono_measure Measure.restrict_le_self)
  have hiP : Integrable (fun y => q y*planeDivergence H y*u y*ψ y)
      (volume.restrict S) := by
    have hi := L2_measure_scalar_test_integrable u
      ((((hq.continuous.mul (planeDivergence_continuous (hH.of_le (by simp)))).mul
        hψ.continuous).memLp_of_hasCompactSupport hc.mul_left).mono_measure
          (ν := volume.restrict S) Measure.restrict_le_self)
    apply hi.congr
    filter_upwards [] with y
    simp only [Pi.mul_apply]
    ring
  have hpoint (y : Plane) :
      ⟪q y • G y+u y • gradient q y,A y (gradient (fun z => q z*ψ z) y)⟫=
      ((q y)^2*⟪G y,A y (gradient ψ y)⟫-q y*planeDivergence H y*u y*ψ y)+
        (⟪G y,F y⟫+u y*planeDivergence F y) := by
    have hdq := hq.differentiable (by simp) y
    have hdψ := hψ.differentiable (by simp) y
    have hdiv : planeDivergence F y=(q y*ψ y)*planeDivergence H y+
        ⟪gradient (fun z => q z*ψ z) y,H y⟫ :=
      planeDivergence_smul (hdq.mul hdψ) (hH.differentiable (by simp) y)
    rw [hdiv,plane_gradient_mul hdq hdψ]
    simp only [F,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,H]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  simp_rw [hpoint]
  have hsum := integral_add (hiV.sub hiP) (hiF.add hiD)
  have hsum2 := integral_add hiF hiD
  simp only [Pi.add_apply,Pi.sub_apply] at hsum hsum2
  rw [hsum,hsum2,hibp]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradientOn.toWeakGradient {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradientOn S u G) : PlaneWeakGradient S u G := by
  intro v ψ hψ hc hs
  have h₁ : (∫ y in S,⟪G y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have h₂ : (∫ y in S,u y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
    simp
  rw [← h₁,← h₂]
  exact hw v ψ hψ hc hs

lemma L2_measure_direction_test_integrable {S : Set Plane}
    (G : Lp Plane 2 (volume.restrict S)) (v : Plane) {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y => ⟪G y,v⟫*ψ y) (volume.restrict S) := by
  have htest : MemLp (fun y => ψ y • v) 2 (volume.restrict S) :=
    ((hψ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right).mono_measure
      Measure.restrict_le_self
  apply (L2_measure_vector_test_integrable G htest).congr
  filter_upwards [] with y
  rw [real_inner_smul_right,mul_comm]

theorem PlaneWeakGradientOn.mul_smooth {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {q : Plane → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    PlaneWeakGradientOn S (fun y => q y*u y)
      (fun y => q y • G y+u y • gradient q y) := by
  intro v ψ hψ hc hs
  let dq : Plane → ℝ := fun y => fderiv ℝ q y v
  let dψ : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hdq : Continuous dq := (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ := L2_measure_direction_test_integrable G v (hq.continuous.mul hψ.continuous) hc.mul_left
  simp only [Pi.mul_apply] at hi₁
  have hi₂ : Integrable (fun y => u y*(q y*dψ y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hq.continuous.mul hdψ).memLp_of_hasCompactSupport
        ((hc.fderiv_apply ℝ v).mul_left)).mono_measure Measure.restrict_le_self)
  have hi₃ : Integrable (fun y => u y*(ψ y*dq y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hψ.continuous.mul hdq).memLp_of_hasCompactSupport hc.mul_right).mono_measure
        Measure.restrict_le_self)
  have he := hw v (fun y => q y*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  have he' : (∫ y in S,⟪G y,v⟫*(q y*ψ y))=
      -((∫ y in S,u y*(q y*dψ y))+(∫ y in S,u y*(ψ y*dq y))) := by
    rw [he,← integral_add hi₂ hi₃]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [fderiv_fun_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul,dq,dψ]
    ring
  have hleft : (∫ y in S,⟪q y • G y+u y • gradient q y,v⟫*ψ y)=
      (∫ y in S,⟪G y,v⟫*(q y*ψ y))+(∫ y in S,u y*(ψ y*dq y)) := by
    rw [← integral_add hi₁ hi₃]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [inner_add_left,real_inner_smul_left,inner_gradient_left,dq]
    ring
  rw [hleft,he']
  have hright : (∫ y in S,q y*u y*fderiv ℝ ψ y v)=(∫ y in S,u y*(q y*dψ y)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [dψ]
    ring
  rw [hright]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.linearize {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hq0 : ∀ y,q y≠0)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
        q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η⊆S → (∫ y,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)))=0 := by
  intro η hη hc hs
  let ψ : Plane → ℝ := fun y => η y/q y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.div hq hq0
  have hsψ : tsupport ψ⊆tsupport η := by
    apply closure_mono
    intro y hy
    change η y≠0
    intro hz
    apply hy
    simp [ψ,hz]
  have hcψ : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hefun : (fun z => q z*ψ z)=η := by
    funext z
    exact mul_div_cancel₀ _ (hq0 z)
  have he := hw.ground_state hA hAs hq hψ hcψ (hsψ.trans hs)
  rw [hJ ψ hψ hcψ (hsψ.trans hs),hefun] at he
  have hi : (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=0 := he.symm
  rw [← hi]
  symm
  calc
    (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=
        ∫ y in S,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hAs,inner_gradient_left]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
      rfl

theorem weak_cmc_graph_jacobi_linearization {S : Set Plane} (hS : IsOpen S)
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) S)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪G y,cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*graphSquaredSecondFundamentalForm g y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η⊆S →
      (∫ y,fderiv ℝ η y (cmcJacobian (gradient g y)
        (cmcWeight (gradient g y) • G y+
          u y • gradient (fun z => cmcWeight (gradient g z)) y)))=0 := by
  apply hw.linearize (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
    (fun y v w => (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _))
    (cmcWeight_contDiff.comp (plane_gradient_contDiff hg))
    (fun y => (cmcWeight_pos _).ne')
  intro ψ hψ hc hs
  rw [← hJ ψ hψ hc hs]
  apply setIntegral_congr_fun hS.measurableSet
  intro y hy
  dsimp only [Function.comp_def]
  rw [cmc_graph_curvature_potential hg hS hlin hy]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceNormalReverse
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

lemma restricted_L2_extension {F : Type*} [NormedAddCommGroup F]
    {S : Set Plane} (hS : MeasurableSet S) (u : Lp F 2 (volume.restrict S)) :
    ∃ U : Lp F 2 (volume : Measure Plane),
      (U : Plane → F) =ᵐ[volume.restrict S] (u : Plane → F) := by
  have hm : MemLp (S.indicator (u : Plane → F)) 2 (volume : Measure Plane) :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp u)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [ae_restrict_of_ae hm.coeFn_toLp, ae_restrict_mem hS] with y hy hys
  exact hy.trans (indicator_of_mem hys _)

theorem PlaneWeakGradientOn.cmc_classical_near
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (G y))) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    HolderJet 1 f 0 ∧ LinearCMCEquationNear f p (fun _ => 0) := by
  obtain ⟨U,hU⟩ := restricted_L2_extension measurableSet_ball u
  obtain ⟨V,hV⟩ := restricted_L2_extension measurableSet_ball G
  have hUV := hw.toWeakGradient.local_congr measurableSet_ball hU hV
  have hVD : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (V y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hd ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hV] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  obtain ⟨H,s,K,β,hs,hsR,hK,hβ,hβ1,hHc,hHe,hHp⟩ :=
    cmc_linearized_holder_gradient hp hpb hR hα hα1 hD hHolder U V hUV hVD
  have hsub : Metric.ball (0 : Plane) s ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hfu' : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hfu
  have hU' : (U : Plane → ℝ) =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hU
  have hwf : PlaneWeakGradient (Metric.ball 0 s) f H :=
    (hUV.mono hsub).local_congr measurableSet_ball
      (hfu'.trans hU'.symm) hHe
  obtain ⟨hfc,hfd⟩ := hwf.holder_C1 hs (hf.mono hsub) hHc hHp
  have hdr (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) (s / 4)) :
      gradient f y = H y := by
    have ht := hwf.continuous_hasFDerivAt hs (hf.mono hsub) hHc hy
    simp only [gradient, ht.fderiv, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨⟨hfc.contDiffAt (Metric.ball_mem_nhds _ (by positivity)),
    s / 4, β, K, by positivity, hβ, hβ1, hK, hfd⟩, s / 4, by positivity, ?_⟩
  intro ψ hψ hc ht
  have hss : Metric.ball (0 : Plane) (s/4) ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (by linarith)
  rw [← hVD ψ hψ hc (ht.trans (hss.trans hsub))]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hHe] with y hy
  by_cases hys : y ∈ Metric.ball (0 : Plane) (s/4)
  · simp only [hdr y hys, hy (hss hys), sub_zero]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (ht hh))]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_memLp_top_ball {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (hf : Continuous f) (R : ℝ) :
    MemLp f ∞ (volume.restrict (Metric.ball (0 : Plane) R)) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_ball).mono fun y hy => hC y (Metric.ball_subset_closedBall hy))

theorem PlaneWeakGradientOn.weighted_L2 {R : ℝ}
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ∃ (v : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R)))
      (J : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))),
      (v =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] fun y => q y * u y) ∧
      (J =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
        fun y => q y • G y + u y • gradient q y) ∧
      PlaneWeakGradientOn (Metric.ball 0 R) v J := by
  have hqL := continuous_memLp_top_ball hq.continuous R
  have hdL := continuous_memLp_top_ball (plane_gradient_contDiff hq).continuous R
  have hv : MemLp (fun y => q y * u y) 2 (volume.restrict (Metric.ball (0 : Plane) R)) :=
    (Lp.memLp u).mul hqL
  have hJ : MemLp (fun y => q y • G y + u y • gradient q y) 2
      (volume.restrict (Metric.ball (0 : Plane) R)) :=
    ((Lp.memLp G).smul hqL).add (hdL.smul (Lp.memLp u))
  refine ⟨hv.toLp _,hJ.toLp _,hv.coeFn_toLp,hJ.coeFn_toLp,?_⟩
  exact (hw.mul_smooth hq).congr hv.coeFn_toLp hJ.coeFn_toLp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalReverseLp_ae (μ : FiniteMeasure NormalBundle) (p : ℝ≥0∞) [Fact (1≤p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Lp F p (μ : Measure NormalBundle)) :
    normalReverseLp μ p u =ᵐ[(μ.map reverseNormal : Measure NormalBundle)] u ∘ reverseNormal :=
  Lp.coeFn_compMeasurePreserving u (reverseNormal_measurePreserving_back μ)

lemma smoothScalarGradient_reverse (f : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarGradient f (reverseNormal z)=smoothScalarGradient f z := by
  change gradient f.val z.1-⟪-(z.2 : Cover),gradient f.val z.1⟫ • -(z.2 : Cover)=_
  rw [inner_neg_left,neg_smul,smul_neg,neg_neg]
  rfl

lemma surfaceJetReverse_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceJetReverse μ (surfaceSmoothJet μ f)=surfaceSmoothJet (μ.map reverseNormal) f := by
  apply Prod.ext
  · apply Lp.ext
    have ha := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle))
    filter_upwards [normalReverseLp_ae μ 2 (surfaceSmoothJet μ f).1,ha,
      (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map reverseNormal : Measure NormalBundle)] with z hz ha hb
    change (surfaceJetReverse μ (surfaceSmoothJet μ f)).1 z=_ at hz
    change (surfaceSmoothJet μ f).1 (reverseNormal z)=smoothScalarValue f (reverseNormal z) at ha
    change (surfaceSmoothJet (μ.map reverseNormal) f).1 z=smoothScalarValue f z at hb
    exact hz.trans (ha.trans hb.symm)
  · apply Lp.ext
    have ha := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
      ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle))
    filter_upwards [normalReverseLp_ae μ 2 (surfaceSmoothJet μ f).2,ha,
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ)
        (μ.map reverseNormal : Measure NormalBundle)] with z hz ha hb
    change (surfaceJetReverse μ (surfaceSmoothJet μ f)).2 z=_ at hz
    change (surfaceSmoothJet μ f).2 (reverseNormal z)=smoothScalarGradient f (reverseNormal z) at ha
    change (surfaceSmoothJet (μ.map reverseNormal) f).2 z=smoothScalarGradient f z at hb
    exact hz.trans (ha.trans ((smoothScalarGradient_reverse f z).trans hb.symm))

theorem surfaceH1_reverse (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) : surfaceJetReverse μ u∈surfaceH1 (μ.map reverseNormal) := by
  apply map_mem_closure (surfaceJetReverse μ).continuous hu
  rintro _ ⟨f,rfl⟩
  exact ⟨f,(surfaceJetReverse_smooth μ f).symm⟩

lemma surfaceMultiplier_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : Lp ℝ 2 (μ : Measure NormalBundle)) :
    surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q) (normalReverseLp μ 2 u)=
      normalReverseLp μ 2 (surfaceMultiplier μ q u) := by
  apply Lp.ext
  have hm := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_lpSMul (r := 2) q u)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (normalReverseLp μ ∞ q) (normalReverseLp μ 2 u),
    normalReverseLp_ae μ ∞ q,normalReverseLp_ae μ 2 u,
    normalReverseLp_ae μ 2 (surfaceMultiplier μ q u),hm] with z hz hq hu hv hm
  change (surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q)
    (normalReverseLp μ 2 u)) z=_ at hz
  change surfaceMultiplier μ q u (reverseNormal z)=_ at hm
  simp only [Function.comp_apply,smul_eq_mul,Pi.mul_apply] at hz hq hu hv hm
  rw [hz,hq,hu,hv,hm]

lemma surfaceJacobiB_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
      (surfaceJetReverse μ u) (surfaceJetReverse μ v)=surfaceJacobiB μ q u v := by
  change ⟪normalReverseLp μ 2 u.2,normalReverseLp μ 2 v.2⟫-
    ⟪surfaceMultiplier (μ.map reverseNormal) (normalReverseLp μ ∞ q)
      (normalReverseLp μ 2 u.1),normalReverseLp μ 2 v.1⟫=_
  rw [surfaceMultiplier_reverse,
    (normalReverseLp μ 2 (F := Cover)).inner_map_map u.2 v.2,
    (normalReverseLp μ 2 (F := ℝ)).inner_map_map (surfaceMultiplier μ q u.1) v.1]
  rfl

lemma surfaceJacobi_homogeneous_of_smooth (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (h : ∀ f : smoothPeriodicScalars,surfaceJacobiB μ q u (surfaceSmoothJet μ f)=0) :
    ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0 := by
  have hc : Continuous (fun v : SurfaceJet μ => surfaceJacobiB μ q u v) :=
    (surfaceJacobiB_continuous μ q).comp (continuous_const.prodMk continuous_id)
  have hr : Set.range (surfaceSmoothJet μ) ⊆ {v | surfaceJacobiB μ q u v=0} := by
    rintro _ ⟨f,rfl⟩
    exact h f
  exact fun v hv => closure_minimal hr (isClosed_eq hc continuous_const) hv

theorem surfaceJacobi_homogeneous_reverse (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hh : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0) :
    ∀ v∈surfaceH1 (μ.map reverseNormal),
      surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u) v=0 := by
  apply surfaceJacobi_homogeneous_of_smooth
  intro f
  calc
    _ = surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u) (surfaceJetReverse μ (surfaceSmoothJet μ f)) :=
      congrArg (surfaceJacobiB (μ.map reverseNormal) (normalReverseLp μ ∞ q)
        (surfaceJetReverse μ u)) (surfaceJetReverse_smooth μ f).symm
    _ = surfaceJacobiB μ q u (surfaceSmoothJet μ f) := surfaceJacobiB_reverse μ q u _
    _ = 0 := hh _ (subset_closure (LinearMap.mem_range_self _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceCurvatureLp_graph_ae (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=σ • (z.2 : Cover))
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {S : Set Plane} (hS : IsOpen S)
    (hcell : ∀ y∈S,∀ i,(a+normalGraph n g y) i∈Icc 0 1)
    (hd : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S)≤μ)
    (hu : ∀ y∈S,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1) :
    (fun y => surfaceCurvatureLp μ N hN (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict S] graphSquaredSecondFundamentalForm g := by
  let Φ : Plane → Cover := fun y => a+normalGraph n g y
  have hΦ : Continuous Φ := continuous_const.add
    ((normalPlaneLinearIsometry n).continuous.add (hg.continuous.smul continuous_const))
  have hmp : Measure.QuasiMeasurePreserving (actualNormalGraphChart a hn g)
      (volume.restrict S) (μ : Measure NormalBundle) :=
    ⟨actualNormalGraphChart_measurable a hn hg.continuous,Measure.absolutelyContinuous_of_le hd⟩
  have hmatchae : (fun y => N (Φ y)) =ᵐ[volume.restrict S]
      fun y => σ • graphSlopeNormal n (gradient g y) := by
    filter_upwards [hmp.ae_eq_comp hae,ae_restrict_mem hS.measurableSet] with y hy hys
    change N (actualNormalGraphChart a hn g y).1=σ •
      ((actualNormalGraphChart a hn g y).2 : Cover) at hy
    rw [actualNormalGraphChart_position a hn g (hcell y hys),actualNormalGraphChart_normal] at hy
    exact hy
  have hmatch : EqOn (fun y => N (Φ y))
      (fun y => σ • graphSlopeNormal n (gradient g y)) S :=
    Measure.eqOn_open_of_ae_eq hmatchae hS (hN.continuous.comp hΦ).continuousOn
      (((graphSlopeNormal_contDiff hn).continuous.comp
        (plane_gradient_contDiff hg).continuous).const_smul σ).continuousOn
  have hq := hmp.ae_eq_comp
    ((show C(NormalBundle,ℝ) from ⟨_,
      (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
      (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle))
  filter_upwards [hq,ae_restrict_mem hS.measurableSet] with y hy hys
  change surfaceCurvatureLp μ N hN (actualNormalGraphChart a hn g y)=
    coverTrace ((fderiv ℝ N (actualNormalGraphChart a hn g y).1).comp
      (fderiv ℝ N (actualNormalGraphChart a hn g y).1)) at hy
  rw [hy,actualNormalGraphChart_position a hn g (hcell y hys)]
  apply graph_normal_extension_curvature a hn hg y hσ hN (hu y hys)
  filter_upwards [hS.mem_nhds hys] with z hz
  exact hmatch hz

lemma surfaceCurvatureLp_reverse (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    normalReverseLp μ ∞ (surfaceCurvatureLp μ N hN)=
      surfaceCurvatureLp (μ.map reverseNormal) N hN := by
  apply Lp.ext
  let Q : C(NormalBundle,ℝ) := ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩
  have hq := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp
    (Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle))
  filter_upwards [normalReverseLp_ae μ ∞ (surfaceCurvatureLp μ N hN),hq,
    Q.coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ.map reverseNormal : Measure NormalBundle)] with z hz hq hr
  exact hz.trans (hq.trans hr.symm)

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

theorem PlaneWeakGradientOn.jacobi_equationNear
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpe : ∀ y ∈ Metric.ball (0 : Plane) R, p y = gradient g y)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hJ : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
      (∫ y in Metric.ball (0 : Plane) R, (cmcWeight (gradient g y))^2 *
        ⟪G y, cmcJacobian (gradient g y) (gradient ψ y)⟫ -
        cmcWeight (gradient g y) * graphSquaredSecondFundamentalForm g y * u y * ψ y) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*f y)
      (gradient g) (fun _ => 0) := by
  let q : Plane → ℝ := fun y => cmcWeight (gradient g y)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  obtain ⟨v,J,hv,hJv,hwJ⟩ := hw.weighted_L2 hq
  have hde := weak_cmc_graph_jacobi_linearization Metric.isOpen_ball hw hg hlin hJ
  have hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (J y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hde ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hJv] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys, hpe y hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  have hvf : (fun y => q y * f y) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      (v : Plane → ℝ) := by
    filter_upwards [hv,hfu] with y hyv hyf
    rw [hyv,hyf]
  have hpContinuous : Continuous p := continuous_iff_continuousAt.mpr fun point => by
    rcases eq_or_ne point 0 with rfl | _
    · exact hpc.continuousAt
    · exact hp.continuousAt
  have heq := (hwJ.cmc_classical_near hpContinuous hpb hR hα hα1 hD hHolder hd
    (hq.continuous.continuousOn.mul hf) hvf).2
  apply heq.congr (Filter.EventuallyEq.rfl) ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hR] with y hy
  exact (hpe y hy).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_jacobi_graph_equationNear
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
    (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ, φ x=1)
    {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    (hqp : (fun y => q (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => u.1 (actualNormalGraphChart a hn g y)) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*f y)
      (gradient g) (fun _ => 0) := by
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  let v := lpPullbackLE hchart hd u.1
  let w := lpPullbackLE hchart hd u.2
  let G := graphCovectorLp hn hgL w
  have hv := lpPullbackLE_ae hchart hd u.1
  have hG : G =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)) := by
    filter_upwards [graphCovectorLp_ae hn hgL w,lpPullbackLE_ae hchart hd u.2] with y hy hz
    change G y=graphCovector n g y (w y) at hy
    change w y=u.2 (actualNormalGraphChart a hn g y) at hz
    rw [hy,hz]
  have hw := surfaceH1_chart_weak_gradient μ a hn hgL Metric.isOpen_ball
    (hg.of_le (by simp)).contDiffOn hcell hd hu
  apply hw.jacobi_equationNear hp hpb hR hα hα1 hD hHolder hpc hg hpe hlin
  · intro ψ hψ hψc hs
    have he := surfaceJacobiB_chart_form μ q u a hn hg.continuous hφ
      (fun x => (hφb x).1) hφO hm (fun y _ => hg.differentiable (by simp) y)
      hχ hc hχO hφχ Metric.isOpen_ball hunit hψ hs
    rw [hhom _ (subset_closure (LinearMap.mem_range_self _ _))] at he
    refine Eq.trans ?_ he.symm
    apply integral_congr_ae
    filter_upwards [hv,hG,hqp] with y hy hz hqz
    change v y=u.1 (actualNormalGraphChart a hn g y) at hy
    rw [hy,hz,hqz]
  · exact hf
  · exact hfu.trans hv.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_graph_equationNear {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=σ • (z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0 < s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
      F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0) := by
  have hm := normalMeasure_graph_area_measure hE hμ a hn hgL
    (fun y _ => ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.continuousAt (x := y)))
    hgraph hφ hsφ hφU hφO hφR hφb
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  have hq := surfaceCurvatureLp_graph_ae μ N hN hσ hae a hn hg Metric.isOpen_ball hcell hd hNu
  apply surfaceH1_jacobi_graph_equationNear μ (surfaceCurvatureLp μ N hN) hu hhom a hn hgL hg
    hφ.continuous.measurable hφb hφO hm hχ hsχ hχO hφχ hs
    (α := 1) (by norm_num) (by norm_num) hD hunit hp.continuous hpb hp.contDiffAt
    (fun y hy => hpe hy) (fun x _ y _ => by simpa only [Real.rpow_one] using hpD x y) hlin hq
  · apply hF.comp
    · exact (continuous_quotientMap.comp
        (continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
          (hg.continuous.smul continuous_const)))).continuousOn
    · exact hS
  · have hmp : Measure.QuasiMeasurePreserving (actualNormalGraphChart a hn g)
        (volume.restrict (Metric.ball (0 : Plane) s)) (μ : Measure NormalBundle) :=
      ⟨actualNormalGraphChart_measurable a hn hg.continuous,Measure.absolutelyContinuous_of_le hd⟩
    filter_upwards [hmp.ae_eq_comp hFu,ae_restrict_mem measurableSet_ball] with y hy hys
    change u.1 (actualNormalGraphChart a hn g y)=
      F (quotientMap (actualNormalGraphChart a hn g y).1) at hy
    rw [actualNormalGraphChart_position a hn g (hcell y hys)] at hy
    exact hy.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_signed_graph_equationNear_oai {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0 < s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
      F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0) := by
  rcases hgraph with hphase | hphase
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x) := by
      simpa only [graphSignedHeight,sub_neg] using hphase
    have hn' : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(1 : ℝ) • (z.2 : Cover) := by
      simpa only [one_smul] using hae
    exact normalMeasure_H1_jacobi_graph_equationNear hE hμ N hN (Or.inl rfl) hn' hu hhom
      a hn hgL hg hgph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hFu
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ graphHeightExtension a n g x<⟪n,x-a⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
    have hcph := graph_superlevel_compl_ae a hn hg.continuous hgph
    have hn' : ∀ᵐ z ∂(μ.map reverseNormal : Measure NormalBundle),
        N z.1=(-1 : ℝ) • (z.2 : Cover) := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [hh] with z hz
      simpa only [Function.comp_apply,reverseNormal,neg_one_smul] using hz
    have hf' : ((surfaceJetReverse μ u).1 : NormalBundle → ℝ)
        =ᵐ[(μ.map reverseNormal : Measure NormalBundle)] F ∘ normalProjection := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hFu
      filter_upwards [normalReverseLp_ae μ 2 u.1,hh] with z hz hh
      exact hz.trans hh
    have hh := surfaceJacobi_homogeneous_reverse μ (surfaceCurvatureLp μ N hN) hhom
    rw [surfaceCurvatureLp_reverse] at hh
    exact normalMeasure_H1_jacobi_graph_equationNear hE.compl (isNormalMeasure_compl hE hμ)
      N hN (Or.inr rfl) hn' (surfaceH1_reverse μ hu) hh
      a hn hgL hg hcph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hf'

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear_oai := @OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear_oai
