-- Prove2me | solution 1 for GlobalTheory.SharpGradient.rhF_le_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:02:03.543002+00:00
-- url     : https://prove2.me/submissions/67605bef-cfb7-44ab-862e-778ec09fdb43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_neg_log_det_le
import Theorems.Thm_GlobalTheory_SharpGradient_rhF_eq_sum_re
import Theorems.Thm_GlobalTheory_SharpGradient_continuous_inv_leadingBlock_entry
import Theorems.Thm_GlobalTheory_SharpGradient_norm_Wm_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Zt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SharpGradient
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x0 ∧ rhF X x0 z ≤ C * ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 := by
  have hZ0 : ∀ τ, ExF.Zt X 0 τ = 0 := by
    intro τ
    have : ExF.Wm X 0 τ = 0 := by
      ext m b
      have h := norm_Wm_sq_le X 0 τ m b
      refine norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (h.trans ?_) (by positivity)))
      refine le_of_eq (Finset.sum_eq_zero fun e _ => ?_)
      split_ifs
      · rw [show (0 : V (nd X)) (Fintype.equivFin (Ent X) e) = 0 from rfl]; simp
      · rfl
    simp [ExF.Zt, this]
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    rw [ExF.mem_OmF_iff X x0 ho]
    intro τ
    simp only [ExF.Am, hZ0, Matrix.zero_mul, sub_zero]
    exact Matrix.PosDef.one
  have e1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x0 := (ExF.isOpen_OmF X x0).mem_nhds h0
  have e2 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ,
      ∑ a, ∑ b, Complex.normSq (ExF.Zt X z τ a b) < 1 / 2 := by
    rw [Filter.eventually_all]
    intro τ
    have hc : Continuous fun z : V (nd X) => ∑ a, ∑ b, Complex.normSq (ExF.Zt X z τ a b) :=
      continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        Complex.continuous_normSq.comp (ExF.cd_Zt X τ a b).continuous
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    simp [hZ0]
  have e3 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ b a,
      ‖(ExF.n1 X z τ)⁻¹ b a‖ < ‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1 := by
    simp only [Filter.eventually_all]
    intro τ b a
    exact (continuous_inv_leadingBlock_entry X τ b a).norm.continuousAt.eventually_lt continuousAt_const
      (lt_add_one _)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨ρ, ∑ τ, 2 * ∑ a, ∑ _m : Fin (r - X.p0),
    (∑ b, (‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1)) ^ 2, hρ, fun z hz => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ := hball (y := z) (by simpa using hz)
  refine ⟨hz1, ?_⟩
  set S := ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  have hW : ∀ τ m b, ‖ExF.Wm X z τ m b‖ ≤ √S := fun τ m b =>
    Real.le_sqrt_of_sq_le (norm_Wm_sq_le X z τ m b)
  rw [rhF_eq_sum_re X x0 ho hz1, Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  refine (neg_log_det_le ((ExF.mem_OmF_iff X x0 ho z).1 hz1 τ) (hz2 τ).le).trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  have hn : ‖ExF.Zt X z τ a m‖ ≤ (∑ b, (‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1)) * √S := by
    rw [ExF.Zt, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul (hz3 τ b a).le (hW τ m b) (norm_nonneg _) (by positivity)
  rw [Complex.normSq_eq_norm_sq]
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hS0]
end GlobalTheory.SharpGradient
