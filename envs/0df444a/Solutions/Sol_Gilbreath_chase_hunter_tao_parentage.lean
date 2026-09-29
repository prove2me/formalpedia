-- Prove2me | solution 1 for Gilbreath.chase_hunter_tao_parentage
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-24T23:41:00.964126+00:00
-- url     : https://prove2.me/submissions/a620a5ef-4dd6-4d35-ba68-93aca47654c9

import Definitions.Def_gilbreath_triangle

namespace Gilbreath

private theorem abs_step_orientation (x y D : ℕ)
    (h : Int.natAbs ((y : ℤ) - (x : ℤ)) = D) :
    y + D = x ∨ x + D = y := by
  omega

private theorem two_value_next (r D x y : ℕ)
    (hr : r < D) (hy : y < 2 * D)
    (hx : x = r ∨ x = r + D)
    (hxy : Int.natAbs ((y : ℤ) - (x : ℤ)) = 0 ∨
      Int.natAbs ((y : ℤ) - (x : ℤ)) = D) :
    y = r ∨ y = r + D := by
  rcases hxy with hz | hd
  · have : y = x := by omega
    omega
  · rcases abs_step_orientation x y D hd with hleft | hright
    · omega
    · omega

/-- The two-value part of Chase--Hunter--Tao, Lemma 3.8. -/
theorem parent_block_two_values (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hbound : ∀ t, t ≤ k → a (n + t) < 2 * D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D) :
    ∃ r, r < D ∧
      ∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D := by
  let r := if a n < D then a n else a n - D
  have hr : r < D := by
    dsimp [r]
    split_ifs with h
    · exact h
    · have hb : a n < 2 * D := by simpa using hbound 0 (by omega)
      omega
  have hstart : a n = r ∨ a n = r + D := by
    dsimp [r]
    split_ifs with h
    · exact Or.inl rfl
    · right
      have hb : a n < 2 * D := by simpa using hbound 0 (by omega)
      omega
  refine ⟨r, hr, ?_⟩
  intro t
  induction t with
  | zero =>
      intro _
      simpa using hstart
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hnextBound := hbound (t + 1) (by omega)
      have hdiff := hchild t (by omega)
      have hstep : Int.natAbs
          ((a (n + t + 1) : ℤ) - (a (n + t) : ℤ)) = 0 ∨
          Int.natAbs
          ((a (n + t + 1) : ℤ) - (a (n + t) : ℤ)) = D := by
        simpa [absDiff, Nat.add_assoc] using hdiff
      have hn := two_value_next r D (a (n + t)) (a (n + t + 1))
        hr (by simpa [Nat.add_assoc] using hnextBound) hprev hstep
      simpa [Nat.add_assoc] using hn

/-- A nonzero child difference forces both parent values to occur. -/
theorem parent_block_attains_both (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hbound : ∀ t, t ≤ k → a (n + t) < 2 * D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D)
    (hatt : ∃ t, t < k ∧ absDiff a (n + t) = D) :
    ∃ r, r < D ∧
      (∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = r) ∧
      (∃ v, v ≤ k ∧ a (n + v) = r + D) := by
  obtain ⟨r, hr, hparent⟩ :=
    parent_block_two_values a n k D hD hbound hchild
  obtain ⟨t, htk, hd⟩ := hatt
  have hl := hparent t (by omega)
  have hr' : a (n + t + 1) = r ∨ a (n + t + 1) = r + D := by
    simpa [Nat.add_assoc] using hparent (t + 1) (by omega)
  have horient : a (n + t + 1) + D = a (n + t) ∨
      a (n + t) + D = a (n + t + 1) := by
    apply abs_step_orientation
    simpa [absDiff, Nat.add_assoc] using hd
  have hpair :
      (a (n + t) = r ∧ a (n + t + 1) = r + D) ∨
      (a (n + t) = r + D ∧ a (n + t + 1) = r) := by
    rcases hl with hl | hl <;> rcases hr' with hr' | hr' <;>
      omega
  rcases hpair with ⟨hl, hr'⟩ | ⟨hl, hr'⟩
  · refine ⟨r, hr, hparent, ⟨t, by omega, hl⟩, ⟨t + 1, by omega, ?_⟩⟩
    simpa [Nat.add_assoc] using hr'
  · refine ⟨r, hr, hparent, ⟨t + 1, by omega, ?_⟩, ⟨t, by omega, hl⟩⟩
    simpa [Nat.add_assoc] using hr'

end Gilbreath

open Gilbreath

theorem solution (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D)
    (hatt : ∃ t, t < k ∧ absDiff a (n + t) = D) :
    (∃ u, u ≤ k ∧ 2 * D ≤ a (n + u)) ∨
    ((∀ t, t ≤ k → a (n + t) = 0 ∨ a (n + t) = D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = 0) ∧
      (∃ v, v ≤ k ∧ a (n + v) = D)) ∨
    (∃ r, 0 < r ∧ r < D ∧
      (∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = r) ∧
      (∃ v, v ≤ k ∧ a (n + v) = r + D)) := by
  by_cases hbig : ∃ u, u ≤ k ∧ 2 * D ≤ a (n + u)
  · exact Or.inl hbig
  · right
    have hbound : ∀ t, t ≤ k → a (n + t) < 2 * D := by
      intro t ht
      by_contra hn
      apply hbig
      exact ⟨t, ht, by omega⟩
    obtain ⟨r, hr, hparent, hattR, hattRD⟩ :=
      parent_block_attains_both a n k D hD hbound hchild hatt
    by_cases hz : r = 0
    · left
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        simpa [hz] using hparent t ht
      · obtain ⟨u, hu, hv⟩ := hattR
        exact ⟨u, hu, by simpa [hz] using hv⟩
      · obtain ⟨v, hv, hw⟩ := hattRD
        exact ⟨v, hv, by simpa [hz] using hw⟩
    · right
      exact ⟨r, by omega, hr, hparent, hattR, hattRD⟩

