-- Prove2me | solution 1 for GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:19.077442+00:00
-- url     : https://prove2.me/submissions/13f7b364-1612-4ad2-9464-2d07251af7eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe
import Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_cexp
import Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_diag_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Nat
noncomputable section
open GlobalTheory GlobalTheory.GaussExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.GaussExpSeries
theorem _root_.solution (B : V →L[ℝ] V →L[ℝ] ℂ) (ε : ℝ)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => Complex.exp (B y y)) x‖ ≤
      n ! * Real.exp (-(ε * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n := by
  have hf : ContDiff ℝ ⊤ (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  refine norm_iteratedFDeriv_comp_le (g := Complex.exp) (f := fun y => B y y) hg hf
    (by exact_mod_cast le_top) x (fun i _ => ?_) (fun i hi _ => ?_)
  · rw [norm_iteratedFDeriv_cexp]; exact Real.exp_le_exp.2 (hB x)
  · refine (norm_iteratedFDeriv_diag_le B i x).trans ?_
    have h1 : 1 ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg x])
    have ha : 1 ≤ (‖B‖ + 1) * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg B]
    have h2 := le_self_pow₀ ha (show i ≠ 0 by omega)
    rw [mul_assoc, mul_pow]
    calc ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) = 2 ^ i * (‖B‖ * (1 + ‖x‖) ^ 2) := by ring
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) := by gcongr; linarith
      _ ≤ 2 ^ i * ((‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by gcongr
end GlobalTheory.GaussExpSeries
