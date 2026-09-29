-- Prove2me | solution 3 for Green_Tao_Theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T20:51:13.152692+00:00
-- url     : https://prove2.me/submissions/f3e7819c-4be1-4c1f-9b22-b3d26fd650e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_green_tao_theorem

namespace GreenTaoDM

def IsAPOfLengthWithDM (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < l)}

def IsAPOfLengthDM (s : Set ℕ) (l : ℕ∞) : Prop := ∃ a d : ℕ, IsAPOfLengthWithDM s l a d

def primeArithmeticProgressionsDM : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > (0 : ℕ∞), IsAPOfLengthDM s l}

end GreenTaoDM

open GreenTaoDM

/-- The Green–Tao theorem, in the set-theoretic packaging of the DeepMind
`formal-conjectures` entry for Erdős problem 219: for every `N` there is a set of primes
which is an arithmetic progression with at least `N` elements.

The arithmetic content is supplied by the platform theorem `green_tao_theorem`, which produces,
for each `k ≥ 1`, a starting point `a` and a common difference `d ≥ 1` with `a + j * d` prime for
all `j < k`.  The work here is to package the progression `{a + n • d | n < k}` as an element of
`primeArithmeticProgressionsDM` and to compute its cardinality, which equals `k` because `d ≥ 1`
makes `n ↦ a + n * d` injective. -/
theorem solution :
    ∀ N : ℕ, ∃ s ∈ primeArithmeticProgressionsDM, (N : ℕ∞) ≤ ENat.card s := by
  intro N
  -- A progression of `max N 1` primes; the `max` guarantees the required positive length.
  obtain ⟨a, d, hd, hp⟩ := green_tao_theorem (max N 1) (le_max_right N 1)
  set k : ℕ := max N 1 with hkdef
  set s : Set ℕ := {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} with hs
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    rintro p ⟨n, hn, rfl⟩
    have hn' : n < k := by exact_mod_cast hn
    simpa [smul_eq_mul] using hp ⟨n, hn'⟩
  -- `s` is the image of `Set.Iio k` under `n ↦ a + n * d`.
  have himg : s = (fun n : ℕ => a + n * d) '' (Set.Iio k) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, by exact_mod_cast hn, by simp [smul_eq_mul]⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, by exact_mod_cast hn, by simp [smul_eq_mul]⟩
  have hinj : Set.InjOn (fun n : ℕ => a + n * d) (Set.Iio k) := by
    intro x _ y _ h
    simp only at h
    have h2 : x * d = y * d := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hcard : ENat.card s = (k : ℕ∞) := by
    have h1 : ENat.card s = Set.encard s := rfl
    rw [h1, himg, hinj.encard_image, show (Set.Iio k) = ↑(Finset.range k) by ext x; simp,
      Set.encard_coe_eq_coe_finsetCard]
    simp
  refine ⟨s, ⟨hprime, (k : ℕ∞), ?_, a, d, hcard, rfl⟩, ?_⟩
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  · rw [hcard]
    exact_mod_cast le_max_left N 1
