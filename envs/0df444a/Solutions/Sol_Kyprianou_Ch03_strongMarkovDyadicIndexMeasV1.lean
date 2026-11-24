-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDyadicIndexMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:17.913077+00:00
-- url     : https://prove2.me/submissions/f246faf0-24a9-4a0c-96e5-c39d25643a63

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n j : ℕ) :
    MeasurableSet[F ((j : NNReal) / (2 : NNReal)^n)]
      {w : Omega | tau w ≠ ⊤ ∧ Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) = j} := by
  classical
  let g : ℕ → NNReal := fun j => (j : NNReal) / (2 : NNReal)^n
  let k : Omega → ℕ := fun w => Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n)
  have hg : StrictMono g := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right (by positivity)).2 (by exact_mod_cast hij)
  have hle (w : Omega) (hw : tau w ≠ ⊤) (j : ℕ) :
      k w ≤ j ↔ tau w ≤ (g j : WithTop NNReal) := by
    rw [hFiniteTime w hw, WithTop.coe_le_coe]
    change Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) ≤ j ↔ finiteTime w ≤ g j
    rw [Nat.ceil_le]
    dsimp [g]
    exact_mod_cast (le_div_iff₀ (show 0 < (2 : ℝ)^n by positivity)).symm
  let A (j : ℕ) : Set Omega := {w | tau w ≤ (g j : WithTop NNReal)}
  let E (j : ℕ) : Set Omega := {w | tau w ≠ ⊤ ∧ k w = j}
  have hA (j : ℕ) : A j = {w | tau w ≠ ⊤ ∧ k w ≤ j} := by
    ext w
    by_cases hw : tau w = ⊤
    · simp [A, hw, WithTop.not_top_le_coe]
      exact WithTop.not_top_le_coe (g j)
    · simpa [A, hw] using (hle w hw j).symm
  have hE (j : ℕ) : MeasurableSet[F (g j)] (E j) := by
    cases j with
    | zero =>
      have he : E 0 = A 0 := by
        rw [hA]
        ext w
        simp [E]
      rw [he]
      exact hTau (g 0)
    | succ j =>
      have he : E (j+1) = A (j+1) \ A j := by
        rw [hA, hA]
        ext w
        change (tau w ≠ ⊤ ∧ k w = j+1) ↔
          (tau w ≠ ⊤ ∧ k w ≤ j+1) ∧ ¬ (tau w ≠ ⊤ ∧ k w ≤ j)
        constructor
        · rintro ⟨hf, hk⟩
          exact ⟨⟨hf, by omega⟩, fun hh => by omega⟩
        · rintro ⟨⟨hf, hk⟩, hn⟩
          exact ⟨hf, by have hh : ¬ k w ≤ j := fun h => hn ⟨hf,h⟩; omega⟩
      rw [he]
      exact (hTau (g (j+1))).diff (F.mono (hg.monotone (Nat.le_succ j)) _ (hTau (g j)))
  exact hE j
