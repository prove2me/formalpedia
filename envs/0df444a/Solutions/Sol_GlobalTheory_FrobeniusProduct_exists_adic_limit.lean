-- Prove2me | solution 1 for GlobalTheory.FrobeniusProduct.exists_adic_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:46:59.696023+00:00
-- url     : https://prove2.me/submissions/07cf8e5d-fdd5-4d3b-b5c3-8751dece7a39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrobeniusProduct
namespace GlobalTheory.FrobeniusProduct
theorem _root_.solution {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  choose N hN using hs
  have tele : ∀ r a b, (∀ k ≥ a, s (k + 1) - s k ∈ I ^ r) → a ≤ b → s b - s a ∈ I ^ r := by
    intro r a b h hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := (I ^ r).add_mem (h b hab) ih
      convert this using 1
      ring
  set N' : ℕ → ℕ := fun r => ∑ j ∈ Finset.range (r + 1), N j with hN'
  have hN'ge : ∀ r, N r ≤ N' r := fun r =>
    Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
  have hN'mono : Monotone N' := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun r => s (N' r)) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsm]
      have := tele m (N' m) (N' n) (fun k hk => hN m k (le_trans (hN'ge m) hk)) (hN'mono hmn)
      have := (I ^ m).neg_mem this
      simpa using this)
  refine ⟨L, fun r => ⟨N' r, fun m hm => ?_⟩⟩
  have h1 := tele r (N' r) m (fun k hk => hN r k (le_trans (hN'ge r) hk)) hm
  have h2 : s (N' r) - L ∈ I ^ r := by
    have := hL r
    rw [SModEq.sub_mem, hsm] at this
    exact this
  have := (I ^ r).add_mem h1 h2
  convert this using 1
  ring
end GlobalTheory.FrobeniusProduct
