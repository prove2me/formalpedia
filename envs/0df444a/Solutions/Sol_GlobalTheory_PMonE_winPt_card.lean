-- Prove2me | solution 1 for GlobalTheory.PMonE.winPt_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:39.200093+00:00
-- url     : https://prove2.me/submissions/f637a1ed-71cd-404e-a19e-bc7266075c9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F)
    (lam π : Fin h → F) (hπ : ∀ j, π j ≠ 0) (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F)
    (hM : ∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) :
    Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} =
      Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  set φ := iterateFrobeniusEquiv F p (h * (L - 1)) with hφ
  have hpow : ∀ y : F, φ y = y ^ (p ^ h) ^ (L - 1) := fun y => by
    rw [hφ, iterateFrobeniusEquiv_def, pow_mul]
  have hN : (p ^ h) ^ (L - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwin : ∀ z : Fin h → F, ∀ j, winPt p π L z j = π j * φ (z j) := fun z j => by
    simp only [winPt, hpow]
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨winPt p π L z.1, fun j => ?_, (hM z.1).1 z.2.2⟩
      invFun := fun x => ⟨fun j => φ.symm (x.1 j / π j), fun j => ?_, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun x => ?_ }
  · rw [hwin, norm_mul, hpow, norm_pow]
    have h0 : 0 ≤ ‖z.1 j‖ := norm_nonneg _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ h0 (z.2.1 j))
  · have hx : ‖φ (φ.symm (x.1 j / π j))‖ ≤ 1 := by
      rw [RingEquiv.apply_symm_apply, norm_div, div_le_one (norm_pos_iff.2 (hπ j))]
      exact x.2.1 j
    rw [hpow, norm_pow] at hx
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN).1 hx
  · rw [hM]
    have : winPt p π L (fun j => φ.symm (x.1 j / π j)) = x.1 := by
      funext j
      rw [hwin, RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
    rw [this]; exact x.2.2
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [mul_div_cancel_left₀ _ (hπ j), RingEquiv.symm_apply_apply]
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
end GlobalTheory.PMonE
