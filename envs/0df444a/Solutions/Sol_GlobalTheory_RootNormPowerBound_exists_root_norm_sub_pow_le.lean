-- Prove2me | solution 1 for GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:36.598518+00:00
-- url     : https://prove2.me/submissions/77deac17-1ef0-4fba-a651-986dc03828a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRootNormSubPowLe
import Theorems.Thm_GlobalTheory_RootNormPowerBound_pow_card_le_norm_eval_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.RootNormPowerBound
open Polynomial
namespace GlobalTheory.RootNormPowerBound
theorem _root_.solution {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by
  have hsp : p.Splits := IsAlgClosed.splits p
  have hcard := hsp.natDegree_eq_card_roots
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb, hmin⟩ := Multiset.exists_min_image (fun a => ‖a - x‖) hne
  refine ⟨b, hb, ?_⟩
  conv_rhs => rw [hsp.eq_prod_roots]
  rw [eval_mul, eval_C, norm_mul, hcard]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)
end GlobalTheory.RootNormPowerBound
