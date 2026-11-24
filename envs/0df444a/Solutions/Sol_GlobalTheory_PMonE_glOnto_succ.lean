-- Prove2me | solution 1 for GlobalTheory.PMonE.glOnto_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:52.621813+00:00
-- url     : https://prove2.me/submissions/86dbd610-ea3b-4593-b8ac-ad09d7798c53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
import Theorems.Thm_GlobalTheory_PMonE_lowerOrder_normal
import Theorems.Thm_GlobalTheory_PMonE_gsum_lowerOrder_inl
import Theorems.Thm_GlobalTheory_PMonE_gsum_lowerOrder_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
namespace GlobalTheory.PMonE
theorem _root_.solution (K : ℕ) (H : GLOnto (K + 1)) : GLOnto (K + 2) := by
  intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩

  obtain ⟨z, hzI, hzs⟩ := H F p (m ⊕ m) e D he (by omega) (lowerOrder (K + 1) M)
    (lowerOrder_normal (by omega) hM) (Sum.elim 0 b) (by
      intro k
      rcases k with k | k
      · simp
      · exact hb k)

  have hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ p ^ e := by
    intro i
    have h0 := congrFun hzs (Sum.inl i)
    rw [gsum_lowerOrder_inl (p ^ e) (by omega)] at h0
    simp only [Sum.elim_inl, Pi.zero_apply] at h0
    have hqK : (p ^ e) ^ K = p ^ (e * K) := (pow_mul p e K).symm
    have h1 : (z (Sum.inl i) ^ p ^ e - z (Sum.inr i)) ^ p ^ (e * K) = 0 := by
      rw [sub_pow_char_pow, ← hqK, ← pow_mul, ← pow_succ']
      exact h0
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h1)).symm
  refine ⟨fun j => z (Sum.inl j), fun j => hzI (Sum.inl j), ?_⟩
  funext i
  rw [← gsum_lowerOrder_inr (p ^ e) (K + 1) D M z hz i, hzs]
  rfl
end GlobalTheory.PMonE
