-- Prove2me | solution 1 for GlobalTheory.SympTower.exists_compatible_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:32.631183+00:00
-- url     : https://prove2.me/submissions/6b1b6a8d-ec0a-4cb8-9024-0e42eac1976e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
import Theorems.Thm_GlobalTheory_SympTower_exists_level
import Theorems.Thm_GlobalTheory_SympTower_ker_and_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  intro F _ ζ hζ hζc g G _ e π hG h1 h2 h3 h4 hπ hcomp
  classical
  have hlev : ∀ M : ℕ, ∃ E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G M.factorial,
      ∀ a b, e _ (E a) (E b) = ζ M.factorial ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := fun M =>
    exists_level M.factorial_pos (hζ _ M.factorial_pos) (e _) (hG _ M.factorial_pos).some
      (h1 _) (h2 _) (h3 _) (h4 _ M.factorial_pos)
  choose E hE using hlev
  have hpush : ∀ n M, 0 < M → n ∣ M → ∀ (x y : G M) (i : ℤ), e M x y = ζ M ^ i →
      e n (π M n x) (π M n y) = ζ n ^ i := by
    rintro n _ hM ⟨m, rfl⟩ x y i h
    have hn : 0 < n := Nat.pos_of_mul_pos_right hM
    have hm : 0 < m := Nat.pos_of_mul_pos_left hM
    rw [hπ n m hn hm, h, ← hζc n m hn hm, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul,
      mul_comm i]
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n, 0 < n → ∀ᶠ k in (U : Filter ℕ), n ∣ k.factorial := by
    intro n hn
    apply Filter.Eventually.filter_mono Filter.hyperfilter_le_cofinite
    rw [Nat.cofinite_eq_atTop]
    exact (Filter.eventually_ge_atTop n).mono fun k hk => Nat.dvd_factorial hn hk
  have hlim : ∀ n, ∃ f : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, 0 < n →
      ∀ a, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = f a := by
    intro n
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      haveI : Finite (G n) := Finite.of_equiv _ (hG n hn).some.symm.toEquiv
      have : ∀ a, ∃ x, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = x := by
        intro a
        obtain ⟨x, hx⟩ := (U.map fun k => π k.factorial n (E k a)).eq_pure_of_finite
        refine ⟨x, ?_⟩
        have : {x} ∈ (U.map fun k => π k.factorial n (E k a)) := by rw [hx]; simp
        exact this
      choose f hf using this
      refine ⟨AddMonoidHom.mk' f fun a b => ?_, fun _ => hf⟩
      obtain ⟨k, hk1, hk2, hk3⟩ := ((hf a).and ((hf b).and (hf (a + b)))).exists
      rw [← hk1, ← hk2, ← hk3, map_add, map_add]
    · exact ⟨0, fun h => absurd h hn⟩
  choose ev hev using hlim
  have hpair : ∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
    intro n hn a b
    obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev n hn b).and (hU n hn))).exists
    rw [← hk1, ← hk2]
    exact hpush n _ k.factorial_pos hk3 _ _ _ (hE k a b)
  have hks := fun n (hn : 0 < n) =>
    ker_and_surj hn (hζ n hn) (e n) (hG n hn).some (h1 n) (ev n) (hpair n hn)
  refine ⟨ev, fun n hn => (hks n hn).1, fun n hn => (hks n hn).2, ?_, hpair⟩
  intro n m hn hm a
  have hnm := Nat.mul_pos hn hm
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev _ hnm a).and (hU _ hnm))).exists
  rw [← hk1, ← hk2]
  exact hcomp _ _ _ hn k.factorial_pos (Dvd.intro _ rfl) hk3 _
end GlobalTheory.SympTower
