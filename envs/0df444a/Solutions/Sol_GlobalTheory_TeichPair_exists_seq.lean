-- Prove2me | solution 1 for GlobalTheory.TeichPair.exists_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:53.344839+00:00
-- url     : https://prove2.me/submissions/cd36c73c-32c8-42c2-ae2e-21031a5cbcb7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
import Theorems.Thm_GlobalTheory_TeichPair_iter_frob
import Theorems.Thm_GlobalTheory_TeichPair_exists_sep
import Theorems.Thm_GlobalTheory_TeichPair_eq_zero_of_ge
import Theorems.Thm_GlobalTheory_TeichPair_ge_pow_sub
import Theorems.Thm_GlobalTheory_TeichPair_ge_l_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_natCast


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
variable {C : Type} [Field C]
namespace GlobalTheory.TeichPair
theorem _root_.solution (V : VF C) (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {O : Type} [CommRing O] {d : ℕ} [NeZero d] (e : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (e a x))
    (hfrob : ∀ a x, V.MM (e (a + 1) x - e a x ^ V.l))
    (hsep : ∀ a a', a ≠ a' → ∃ x, V.v (e a x - e a' x) = 0)
    (hunr : ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (e a ε - 1)) ∧
      ∀ x : O, (∀ a, V.MM (e a x)) → ∃ y, ε * x = (V.l : O) * y) :
    ∃ (s : ℕ → O) (N : ℕ) (ζ : ZMod d → C), (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ V.v (N : C) = 0 ∧
      (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧
      ∀ a (n : ℕ), V.Ge n (ζ a - e a (s n)) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hq : 2 ≤ V.l ^ d := le_trans hl (Nat.le_self_pow (NeZero.ne d) _)
  obtain ⟨N, hN⟩ : ∃ N, V.l ^ d = N + 2 := ⟨V.l ^ d - 2, by omega⟩
  let π := Ideal.Quotient.mk (maxId V)
  have hπ : ∀ a b : intRing V, π a = π b ↔ V.MM ((a : C) - b) := fun a b => Ideal.Quotient.eq
  let e' : ZMod d → O →+* intRing V := fun a => (e a).codRestrict (intRing V) (hint a)
  let f : ZMod d → O →+* (intRing V ⧸ maxId V) := fun a => π.comp (e' a)
  have hf : ∀ a x, f (a + 1) x = f a x ^ V.l := fun a x => by
    show π _ = π _ ^ _
    rw [← map_pow, hπ]
    exact hfrob a x
  have hs : ∀ a a', a ≠ a' → ∃ x, f a x ≠ f a' x := fun a a' h => by
    obtain ⟨x, hx⟩ := hsep a a' h
    refine ⟨x, fun h' => ?_⟩
    have h2 : 0 < V.v (e a x - e a' x) := (hπ _ _).1 h'
    rw [hx] at h2
    exact lt_irrefl _ h2
  obtain ⟨x, hx0, hxi⟩ := exists_sep hl f hf hs
  obtain ⟨ε, ⟨y, hy⟩, hε1, hε⟩ := hunr
  have hd : ∀ a x, f a x ^ V.l ^ d = f a x := fun a x => by
    rw [← iter_frob f hf]; simp
  have hfε : ∀ a, f a ε = 1 := fun a => by
    show π _ = 1
    rw [← map_one π, hπ]
    exact hε1 a
  have hεp : ∀ m : ℕ, (V.l : O) ∣ ε ^ (m + 1) - ε := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      have : ε ^ (m + 1 + 1) - ε = ε * (ε ^ (m + 1) - ε) + (ε * ε - ε) := by ring
      rw [this, hy]
      exact dvd_add (ih.mul_left _) (dvd_mul_right _ _)
  have hb : (V.l : O) ∣ (ε * x) ^ V.l ^ d - ε * x := by
    obtain ⟨z, hz⟩ := hε (x ^ V.l ^ d - x) fun a => by
      have h1 : π (e' a (x ^ V.l ^ d)) = π (e' a x) := by
        show f a _ = f a _
        rw [map_pow, hd]
      rw [map_sub]
      exact (hπ _ _).1 h1
    have : (ε * x) ^ V.l ^ d - ε * x = (ε ^ (N + 1 + 1) - ε) * x ^ V.l ^ d + ε * (x ^ V.l ^ d - x) := by
      rw [mul_pow, show N + 1 + 1 = V.l ^ d by omega]; ring
    rw [this, hz]
    exact dvd_add ((hεp _).mul_right _) (dvd_mul_right _ _)
  let s : ℕ → O := fun n => (ε * x) ^ V.l ^ (d * n)
  have hs1 : ∀ n, s (n + 1) = s n ^ V.l ^ d := fun n => by
    simp only [s]
    rw [← pow_mul, ← pow_add, mul_add, mul_one]
  have hsc : ∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y := fun n => by
    have h1 := dvd_sub_pow_of_dvd_sub hb (d * n)
    have h2 : s (n + 1) = ((ε * x) ^ V.l ^ d) ^ V.l ^ (d * n) := by
      simp only [s]
      rw [← pow_mul, ← pow_add, mul_add, mul_one, add_comm]
    rw [h2]
    refine dvd_trans (pow_dvd_pow _ ?_) h1
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    nlinarith
  have hlim : ∀ a, ∃ z, ∀ n : ℕ, V.Ge n (z - e a (s n)) := fun a => cpl (fun n => e a (s n)) fun n => by
    obtain ⟨z, hz⟩ := hsc n
    rw [← map_sub, hz, map_mul, map_pow, map_natCast]
    simpa using (ge_l_pow V n).mul (hint a z)
  choose ζ hζ using hlim
  have hζi : ∀ a, V.Ge 0 (ζ a) := fun a => by
    have := (hζ a 0).add (by simpa using hint a (s 0))
    simpa using this
  have hζq : ∀ a, ζ a ^ V.l ^ d = ζ a := fun a => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    have h1 := ge_pow_sub (hζi a) (hint a _) (hζ a n) (V.l ^ d)
    have h2 := (hζ a (n + 1)).mono (w' := n) (by push_cast; linarith)
    rw [hs1, map_pow] at h2
    simpa using h1.sub h2
  let ζ' : ZMod d → intRing V := fun a => ⟨ζ a, hζi a⟩
  have hζπ : ∀ a, π (ζ' a) = f a x := fun a => by
    have h1 : π (ζ' a) = f a (s 1) := by
      refine (hπ _ _).2 (lt_of_lt_of_le ?_ (hζ a 1))
      exact_mod_cast WithTop.coe_lt_coe.2 (zero_lt_one' ℝ)
    rw [h1, hs1, map_pow, hd]
    simp [s, hfε]
  have hζ0 : ∀ a, ζ a ≠ 0 := fun a h => by
    apply hx0 a
    rw [← hζπ, show ζ' a = 0 from Subtype.ext h, map_zero]
  have hζN : ∀ a, ζ a ^ (N + 1) = 1 := fun a => by
    apply mul_right_cancel₀ (hζ0 a)
    rw [← pow_succ, one_mul, show N + 1 + 1 = V.l ^ d by omega, hζq]
  have hlπ : ((V.l : ℕ) : intRing V ⧸ maxId V) = 0 := by
    rw [← map_natCast π, ← map_zero π, hπ]
    show 0 < V.v _
    simp [V.v_l]
  have hNπ : ((N + 1 : ℕ) : intRing V ⧸ maxId V) ≠ 0 := fun h => by
    have h1 : ((N + 1 + 1 : ℕ) : intRing V ⧸ maxId V) = 0 := by
      rw [show N + 1 + 1 = V.l ^ d by omega, Nat.cast_pow, hlπ, zero_pow (NeZero.ne d)]
    rw [Nat.cast_succ, h, zero_add] at h1
    exact one_ne_zero h1
  refine ⟨s, N + 1, ζ, hsc, ?_, hζN, fun a a' h => hxi ?_, fun a => ?_, hζ⟩
  · refine le_antisymm (not_lt.1 fun h => hNπ ?_) (VF.ge_natCast (V := V) _)
    rw [← map_natCast π, ← map_zero π, hπ]
    show 0 < V.v _
    simpa using h
  · show f a x = f a' x
    rw [← hζπ, ← hζπ, show ζ' a = ζ' a' from Subtype.ext h]
  · by_contra hne
    have h1 := geom_sum₂_mul (ζ' (a + 1)) (ζ' a ^ V.l) (N + 1)
    have h2 : ζ' (a + 1) ^ (N + 1) - (ζ' a ^ V.l) ^ (N + 1) = 0 := by
      apply Subtype.ext
      show ζ (a + 1) ^ (N + 1) - (ζ a ^ V.l) ^ (N + 1) = 0
      rw [← pow_mul, mul_comm, pow_mul, hζN, hζN, one_pow, sub_self]
    rw [h2, mul_eq_zero, sub_eq_zero] at h1
    rcases h1 with h1 | h1
    · have h3 := congrArg π h1
      rw [map_sum, map_zero] at h3
      simp only [map_mul, map_pow, hζπ, ← hf] at h3
      rw [geom_sum₂_self] at h3
      exact mul_ne_zero hNπ (pow_ne_zero _ (hx0 _)) h3
    · exact hne (congrArg Subtype.val h1)
end GlobalTheory.TeichPair
