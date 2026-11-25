-- Prove2me | solution 1 for GlobalTheory.GaussDerivBound.weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:50:59.923312+00:00
-- url     : https://prove2.me/submissions/37710323-03b7-4e19-af12-f7a9047b41ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBounded
import Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_diag_le__858662257094
import Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94
import Theorems.Thm_P2M_GlobalTheory_GaussDerivBound_exists_bound_poly_mul_exp__b46fcb63c6bf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussDerivBound
open scoped Nat
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.GaussDerivBound
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  intro E _ _ c α hc hα k m
  set B : E →L[ℝ] E →L[ℝ] ℝ := (-c) • innerSL ℝ with hBdef
  have hBy : ∀ y : E, B y y = -(c * ‖y‖ ^ 2) := fun y => by
    simp [hBdef, real_inner_self_eq_norm_sq]
    left
    first | exact real_inner_self_eq_norm_sq y | simp [innerSL_apply, real_inner_self_eq_norm_sq] | rfl
  have hfun : (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) =
      Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y) := by
    funext y
    simp only [Function.comp_apply, Complex.ofRealLI_apply, hBy, Complex.ofReal_exp, Complex.ofReal_neg]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  have hc' : 0 < c * (1 - α) := mul_pos hc (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp' (c * (1 - α)) hc' (k + 2 * m)
  refine ⟨m ! * (2 * (‖B‖ + 1)) ^ m * C, fun x => ?_⟩
  have hn : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [hfun, LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp' i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le' B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  rw [hBy x] at hfb
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  have hexp : Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2) =
      Real.exp (-(c * (1 - α) * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (Real.exp ∘ fun y : E => B y y) x‖ * Real.exp (c * α * ‖x‖ ^ 2)
      ≤ (1 + ‖x‖) ^ k * (m ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m) *
          Real.exp (c * α * ‖x‖ ^ 2) := by
        gcongr
        linarith
    _ = m ! * (2 * (‖B‖ + 1)) ^ m * ((1 + ‖x‖) ^ (k + 2 * m) *
          (Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp (c * α * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ m = (2 * (‖B‖ + 1)) ^ m * (1 + ‖x‖) ^ (2 * m) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ m ! * (2 * (‖B‖ + 1)) ^ m * C := by
        rw [hexp]
        gcongr
        exact hC ‖x‖ hx0
end GlobalTheory.GaussDerivBound
