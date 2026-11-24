-- Prove2me | solution 1 for GlobalTheory.MonicSeparableProduct.monic_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:58:14.526957+00:00
-- url     : https://prove2.me/submissions/a6efaf1d-b71f-4d53-aca6-a6d99631d2ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MonicSeparableProduct
open Polynomial
namespace GlobalTheory.MonicSeparableProduct
theorem _root_.solution {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) :
    ∀ (n : ℕ) (f : W[X]), f.Monic → f.natDegree = n →
      ∃ M : Multiset W, f = (M.map (fun r => X - C r)).prod := by
  intro n
  induction n with
  | zero =>
    intro f hf h0
    exact ⟨0, by simpa using (hf.natDegree_eq_zero).1 h0⟩
  | succ n ih =>
    intro f hf hn
    have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
    have hdeg : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hf.ne_zero, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective (algebraMap W F) hinj f hdeg
    have hint : IsIntegral W x := ⟨f, hf, hx⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hroot : f.IsRoot r := by
      apply hinj
      rw [map_zero, ← hx, ← hr, eval₂_at_apply]
    have hfac := mul_divByMonic_eq_iff_isRoot.2 hroot
    have hq : (f /ₘ (X - C r)).Monic := by
      apply Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfac]; exact hf
    have hqd : (f /ₘ (X - C r)).natDegree = n := by
      rw [natDegree_divByMonic f (monic_X_sub_C r), hn, natDegree_X_sub_C]
      simp
    obtain ⟨M, hM⟩ := ih _ hq hqd
    refine ⟨r ::ₘ M, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hM, hfac]
end GlobalTheory.MonicSeparableProduct
