-- Prove2me | solution 1 for GlobalTheory.TeichPair.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:32.315095+00:00
-- url     : https://prove2.me/submissions/eddab3c8-42af-4cfc-8c11-4533c69ed516

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
import Theorems.Thm_GlobalTheory_TeichPair_iter_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
namespace GlobalTheory.TeichPair
theorem _root_.solution {k O : Type} [CommRing k] [IsDomain k] [CommRing O] {d : ℕ} [NeZero d] {l : ℕ} (hl : 2 ≤ l)
    (f : ZMod d → O →+* k) (hf : ∀ a x, f (a + 1) x = f a x ^ l)
    (hsep : ∀ a a', a ≠ a' → ∃ x, f a x ≠ f a' x) :
    ∃ x, (∀ a, f a x ≠ 0) ∧ Function.Injective fun a => f a x := by
  have hq : 2 ≤ l ^ d := le_trans hl (Nat.le_self_pow (NeZero.ne d) l)
  have hv : ∀ a x, f a x = f 0 x ^ l ^ a.val := fun a x => by
    rw [← iter_frob f hf]; simp
  have hd : ∀ x, f 0 x ^ l ^ d = f 0 x := fun x => by
    rw [← iter_frob f hf]; simp
  obtain ⟨N, hN⟩ : ∃ N, l ^ d = N + 2 := ⟨l ^ d - 2, by omega⟩
  have hu : ∀ x, f 0 x ≠ 0 → f 0 x ^ (N + 1) = 1 := fun x hx => by
    apply mul_right_cancel₀ hx
    rw [← pow_succ, one_mul, show N + 1 + 1 = l ^ d by omega, hd]
  let H : Subgroup kˣ :=
    { carrier := {u | ∃ x, f 0 x = u}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x * y, by simp [hx, hy]⟩
      inv_mem' := by
        rintro a ⟨x, hx⟩
        refine ⟨x ^ N, ?_⟩
        have h1 := hu x (by rw [hx]; exact a.ne_zero)
        rw [map_pow, hx]
        rw [hx, pow_succ] at h1
        exact (Units.inv_eq_of_mul_eq_one_left h1).symm }
  have hH : H ≤ rootsOfUnity (N + 1) k := by
    rintro a ⟨x, hx⟩
    rw [mem_rootsOfUnity', ← hx]
    exact hu x (by rw [hx]; exact a.ne_zero)
  haveI : IsCyclic H := Subgroup.isCyclic_of_le hH
  obtain ⟨⟨γ, x, hx⟩, hγ⟩ := IsCyclic.exists_zpow_surjective (G := H)
  have hx0 : f 0 x ≠ 0 := by rw [hx]; exact γ.ne_zero
  refine ⟨x, fun a => by rw [hv]; exact pow_ne_zero _ hx0, fun a a' h => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := hsep a a' hne
  apply hy
  have hl0 : ∀ m : ℕ, l ^ m ≠ 0 := fun m => pow_ne_zero _ (by omega)
  by_cases hy0 : f 0 y = 0
  · rw [hv a, hv a', hy0, zero_pow (hl0 _), zero_pow (hl0 _)]
  · have h1 := hu y hy0
    rw [pow_succ] at h1
    let w : kˣ := Units.mkOfMulEqOne (f 0 y) (f 0 y ^ N) (by rw [mul_comm]; exact h1)
    obtain ⟨m, hm⟩ := hγ ⟨w, y, rfl⟩
    have hm' : γ ^ m = w := congrArg Subtype.val hm
    have h2 : γ ^ l ^ a.val = γ ^ l ^ a'.val := by
      apply Units.ext
      have h' : f a x = f a' x := h
      rw [hv a, hv a', hx] at h'
      simpa using h'
    have h3 : w ^ l ^ a.val = w ^ l ^ a'.val := by
      rw [← hm', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m, mul_comm m, zpow_mul, zpow_mul,
        zpow_natCast, zpow_natCast, h2]
    have h4 := congrArg Units.val h3
    rw [hv a, hv a']
    simpa [w] using h4
end GlobalTheory.TeichPair
