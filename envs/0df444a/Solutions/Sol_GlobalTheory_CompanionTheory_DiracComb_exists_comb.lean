-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DiracComb.exists_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:53.977901+00:00
-- url     : https://prove2.me/submissions/b2dd49f5-f131-4ac9-8fa9-cec84d7c1d3e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_summable_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb
namespace GlobalTheory.CompanionTheory.DiracComb
theorem _root_.solution : ∀ (n : ℕ), ∃ S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, S f = ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by
  intro n
  have hb : ∀ (f : SchwartzMap (Fin n → ℝ) ℂ) (x : Fin n → ℝ), ‖f x‖ ≤
      (2 ^ (2 * n) * (Finset.Iic (2 * n, 0)).sup (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ) f) *
        ((1 + ‖x‖) ^ (2 * n))⁻¹ := by
    intro f x
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2 * n, 0)) (k := 2 * n)
      (n := 0) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at this
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact this
  have hs : ∀ f : SchwartzMap (Fin n → ℝ) ℂ,
      Summable fun m : Fin n → ℤ => ‖f (fun i => (m i : ℝ))‖ := fun f =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hb f _)
      ((summable_weight n).mul_left _)
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ))) (fun f g => ?_) (fun a f => ?_) ?_,
    fun f => rfl⟩
  · exact (hs f).of_norm.tsum_add (hs g).of_norm
  · exact tsum_mul_left
  · refine ⟨Finset.Iic (2 * n, 0),
      2 ^ (2 * n) * ∑' m : Fin n → ℤ, ((1 + ‖(fun i => (m i : ℝ))‖) ^ (2 * n))⁻¹,
      by positivity, fun f => ?_⟩
    refine (tsum_of_norm_bounded ((summable_weight n).mul_left _).hasSum (fun m => hb f _)).trans ?_
    rw [tsum_mul_left]
    exact le_of_eq (by ring)
end GlobalTheory.CompanionTheory.DiracComb
