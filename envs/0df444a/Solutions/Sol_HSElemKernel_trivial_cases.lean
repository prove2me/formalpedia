-- Prove2me | solution 1 for HSElemKernel.trivial_cases
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T21:58:34.44703+00:00
-- url     : https://prove2.me/submissions/dca1d5b2-beb8-46d7-89c6-7dfafb7e92ef

import Mathlib
import Definitions.Def_HSElemKernel_IsYes

open HSElemKernel

/-- A hitting set never hits the empty set: `(Z ∩ ∅).Nonempty` is impossible. -/
lemma no_hit_empty {α : Type*} [DecidableEq α] (Z : Finset α) : ¬ (Z ∩ (∅ : Finset α)).Nonempty := by
  simp

/-- If `∅ ∉ S`, then `Finset.univ` meets every input set, because every `A ∈ S` is nonempty. -/
lemma univ_hits (I : HSInstance) (hne : ∅ ∉ I.S) : ∀ A ∈ I.S, (Finset.univ ∩ A).Nonempty := by
  intro A hA
  simpa [Finset.inter_univ] using
    Finset.nonempty_iff_ne_empty.2 (by intro h; exact hne (by simpa [h] using hA))

namespace P2MHole01_eb4b3341
theorem solution (I : HSInstance) (hk : I.k = (1 : ℕ)) (hSne : I.S ≠ ∅) (H : IsYes I) :
  ∃ (u : Fin I.n), ∀ A ∈ I.S, u ∈ A := by
  obtain ⟨Z, hZc, hZ⟩ := H
  have hZc1 : Z.card ≤ 1 := by simpa [hk] using hZc
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ ∈ I.S := Finset.nonempty_iff_ne_empty.2 hSne
  obtain ⟨u, hu⟩ : ∃ u, u ∈ Z ∩ A₀ := hZ A₀ hA₀
  have ⟨huZ, _⟩ : u ∈ Z ∧ u ∈ A₀ := by simpa using hu
  have hZu : Z = {u} := by
    have hZ1 : Z.card = 1 := by
      have hpos : 0 < Z.card := Finset.card_pos.mpr ⟨u, huZ⟩
      omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hZ1
    have hua : u = w := by
      rw [hw] at huZ
      simpa [Finset.mem_singleton] using huZ
    rw [hw, hua]
  use u
  intro A hA
  obtain ⟨v, hv⟩ := hZ A hA
  have ⟨hvZ, hvA⟩ : v ∈ Z ∧ v ∈ A := by simpa using hv
  have hvu : v = u := by
    rw [hZu] at hvZ
    simpa [Finset.mem_singleton] using hvZ
  rw [hvu] at hvA
  exact hvA
end P2MHole01_eb4b3341

/-- -- riskiest
With `k = 1` and `S ≠ ∅`, any hitting set has at most one element, and that element
lies in every input set. -/
lemma hit_singleton (I : HSInstance) (hk : I.k = 1) (hSne : I.S ≠ ∅) (H : IsYes I) :
    ∃ u : Fin I.n, ∀ A ∈ I.S, u ∈ A := by
  (first | exact P2MHole01_eb4b3341.solution I hk hSne H | (apply P2MHole01_eb4b3341.solution <;> assumption))

/-- If `u ∈ A`, then the singleton `{u}` hits `A`. -/
lemma singleton_hits {α : Type*} [DecidableEq α] (A : Finset α) (u : α) (hu : u ∈ A) :
    ({u} ∩ A).Nonempty := by
  exact ⟨u, by simp [hu]⟩

/-- **Section 2.1, trivial cases** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.1, p.3): for every Hitting Set instance
`(U, S, k)`,
1. if `∅ ∈ S`, it is a NO-instance;
2. if `S = ∅`, it is a YES-instance;
3. if `k = 0` and `S ≠ ∅`, it is a NO-instance;
4. if `∅ ∉ S` and `k ≥ |U|`, it is a YES-instance;
5. if `k = 1`, it is a YES-instance iff `S = ∅` or the input sets have a common element.

**Formalization Note** Clause 5 is what the page's test "we check whether the input sets have a
common element" decides; the disjunct `S = ∅` keeps it true when `U = ∅`. -/
theorem solution (I : HSInstance) :
    (∅ ∈ I.S → ¬ IsYes I) ∧ (I.S = ∅ → IsYes I) ∧ (I.k = 0 → I.S ≠ ∅ → ¬ IsYes I) ∧
      (∅ ∉ I.S → I.n ≤ I.k → IsYes I) ∧
      (I.k = 1 → (IsYes I ↔ I.S = ∅ ∨ ∃ u : Fin I.n, ∀ A ∈ I.S, u ∈ A)) := by
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5⟩
  · -- 1. ∅ ∈ S: no hitting set meets ∅
    intro hE
    by_contra H
    obtain ⟨Z, hZc, hZA⟩ := H
    exact no_hit_empty Z (hZA ∅ hE)
  · -- 2. S = ∅: the empty set Z hits vacuously
    intro hS
    refine ⟨∅, Nat.zero_le _, fun A hA => by simp [hS] at hA⟩
  · -- 3. k = 0: a hitting set has size ≤ 0, hence is ∅, and cannot meet any A ∈ S
    intro hK hSne
    by_contra H
    obtain ⟨Z, hZc, hZA⟩ := H
    have hZc0 : Z.card ≤ 0 := by simpa [hK] using hZc
    have hZ : Z = ∅ := by
      apply Finset.card_eq_zero.1
      omega
    obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.2 hSne
    have hBad : (Z ∩ A).Nonempty := hZA A hA
    rw [hZ] at hBad
    exact no_hit_empty ∅ hBad
  · -- 4. ∅ ∉ S and n ≤ k: Z = Finset.univ works
    intro hne hn
    refine ⟨Finset.univ, by simpa [Finset.card_univ] using hn, fun A hA => ?_⟩
    simpa [Finset.inter_univ] using univ_hits I hne A hA
  · -- 5. k = 1
    intro hK
    refine ⟨fun H => ?_, fun H => ?_⟩
    · by_cases hS : I.S = ∅
      · exact Or.inl hS
      · exact Or.inr (hit_singleton I hK hS H)
    · cases H with
      | inl hS =>
        refine ⟨∅, Nat.zero_le _, fun A hA => by simp [hS] at hA⟩
      | inr hu =>
        obtain ⟨u, hu⟩ := hu
        refine ⟨{u}, by simp [hK], fun A hA => singleton_hits A u (hu A hA)⟩
