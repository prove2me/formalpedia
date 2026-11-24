-- Prove2me | solution 1 for GlobalTheory.iteratedDeriv_zero_eq_zero_of_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:15.14293+00:00
-- url     : https://prove2.me/submissions/ae8772d6-22fb-412b-b074-9f9c335777bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))
end GlobalTheory
