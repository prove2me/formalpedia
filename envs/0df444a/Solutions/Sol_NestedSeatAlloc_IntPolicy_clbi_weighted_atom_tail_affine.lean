-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_weighted_atom_tail_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:54:03.816712+00:00
-- url     : https://prove2.me/submissions/1ae86575-0f5e-43bb-849b-7896e5e412c4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n m : ℕ) (c a tailWeight tailRevenue : ℝ)
    (w : ℕ → ℝ) (g H : ℝ → ℝ)
    (hunit : ∀ i : ℕ, i ≤ n → ∃ ai bi : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        g (s - i) = ai + bi * (s - i))
    (hexpect : ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
      H s = (∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + g (s - i))) +
        tailWeight * ((s - a) * c + tailRevenue)) :
    ∃ A B : ℝ, ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1), H s = A + B * s := by
  classical
  have hchoices : ∀ i : ℕ, ∃ ai bi : ℝ,
      (if hi : i ≤ n then
        ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
          g (s - i) = ai + bi * (s - i)
       else True) := by
    intro i
    by_cases hi : i ≤ n
    · rcases hunit i hi with ⟨ai, bi, hab⟩
      exact ⟨ai, bi, by simpa [hi] using hab⟩
    · exact ⟨0, 0, by simp [hi]⟩
  choose A B hAB using hchoices
  let alpha : ℝ :=
    (∑ i ∈ Finset.range (n + 1),
      w i * ((i : ℝ) * c + A i - B i * i)) +
      tailWeight * (tailRevenue - c * a)
  let beta : ℝ := (∑ i ∈ Finset.range (n + 1), w i * B i) + tailWeight * c
  refine ⟨alpha, beta, ?_⟩
  intro s hs
  have hterms :
      (∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + g (s - i))) =
      ∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + A i + B i * (s - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by
      have hirange := Finset.mem_range.mp hi
      omega
    have hAi : ∀ x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        g (x - i) = A i + B i * (x - i) := by
      simpa [hin] using hAB i
    rw [hAi s hs]
    ring
  have hAtoms :
      (∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + A i + B i * (s - i))) =
      (∑ i ∈ Finset.range (n + 1),
        w i * ((i : ℝ) * c + A i - B i * i)) +
        (∑ i ∈ Finset.range (n + 1), w i * B i) * s := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1),
          (w i * ((i : ℝ) * c + A i - B i * i) +
            (w i * B i) * s) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i ∈ Finset.range (n + 1),
            w i * ((i : ℝ) * c + A i - B i * i)) +
          ∑ i ∈ Finset.range (n + 1), (w i * B i) * s :=
            Finset.sum_add_distrib
      _ = (∑ i ∈ Finset.range (n + 1),
            w i * ((i : ℝ) * c + A i - B i * i)) +
          (∑ i ∈ Finset.range (n + 1), w i * B i) * s := by
            rw [← Finset.sum_mul]
  rw [hexpect s hs, hterms, hAtoms]
  simp only [alpha, beta]
  ring
