-- Prove2me | solution 1 for GlobalTheory.CardLength.log_card_eq_finsum_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:22.432653+00:00
-- url     : https://prove2.me/submissions/cf65b95f-632d-4992-81d9-c83b17d563c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
import Theorems.Thm_GlobalTheory_CardLength_card_eq_prod_lenAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]
namespace GlobalTheory.CardLength
theorem _root_.solution : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  intro B _ N _ _ _
  classical
  obtain ⟨k, hk, hc⟩ := card_eq_prod_lenAt (R := B) _ N rfl
  have hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m := fun m => by
    have h := hk m
    unfold lenAt at h
    rw [h]; rfl
  simp_rw [hlen]
  rw [finsum_eq_sum_of_support_subset (s := k.support) _ ?_]
  · have h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0 := by
      rw [← hc]; exact Nat.card_pos.ne'
    rw [Finsupp.prod, Finset.prod_ne_zero_iff] at h0
    rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro m hm
      exact_mod_cast h0 m hm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0; apply hm; simp [h0]
end GlobalTheory.CardLength
