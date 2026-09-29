-- Prove2me | solution 1 for MegiddoLP.FixedDim.one_query_halves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:49:56.635738+00:00
-- url     : https://prove2.me/submissions/9119599c-23e4-4a2b-b902-f3dc79065d51

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

namespace MegiddoLP.FixedDim

/-- Existence of a median: a real `m` with at least half of the values `≥ m` and at least
half of the values `≤ m`. -/
theorem aux_oqh_median (n : ℕ) (c : Fin n → ℝ) :
    ∃ m : ℝ, n ≤ 2 * (Finset.univ.filter fun i => m ≤ c i).card ∧
      n ≤ 2 * (Finset.univ.filter fun i => c i ≤ m).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, by simp, by simp⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
  set S := Finset.univ.filter
    (fun i => n ≤ 2 * (Finset.univ.filter fun j => c i ≤ c j).card) with hS
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ c hne
  have hSne : S.Nonempty := by
    refine ⟨i0, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : (Finset.univ.filter fun j => c i0 ≤ c j) = Finset.univ := by
      ext j; simp [hi0 j (Finset.mem_univ _)]
    rw [this, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hkS, hk⟩ := Finset.exists_max_image S c hSne
  refine ⟨c k, (Finset.mem_filter.1 hkS).2, ?_⟩
  by_contra hcon
  push Not at hcon
  set T := Finset.univ.filter fun j => c k < c j with hT
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun j => c k < c j)
  have hneg : (Finset.univ.filter fun j => ¬ c k < c j) =
      Finset.univ.filter fun j => c j ≤ c k := by
    ext j; simp
  rw [hneg, Finset.card_univ, Fintype.card_fin, ← hT] at hsplit
  have hTpos : 0 < T.card := by omega
  have hTne : T.Nonempty := Finset.card_pos.1 hTpos
  obtain ⟨j', hj'T, hj'⟩ := Finset.exists_min_image T c hTne
  have hj'gt : c k < c j' := (Finset.mem_filter.1 hj'T).2
  have hEq : (Finset.univ.filter fun j => c j' ≤ c j) = T := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT]
    constructor
    · intro h; exact lt_of_lt_of_le hj'gt h
    · intro h
      exact hj' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hj'S : j' ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hEq]
    omega
  have := hk j' hj'S
  linarith

end MegiddoLP.FixedDim

open MegiddoLP.FixedDim

theorem solution (n : ℕ) (a : Fin n → Fin 1 → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree 1 (Fin n → Option Ordering), ∀ x : Fin 1 → ℝ,
      T.numQueries x ≤ 1 ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n ≤ 2 * (Finset.univ.filter fun i => (T.eval x i).isSome).card := by
  have ha0 : ∀ i, a i 0 ≠ 0 := by
    intro i h
    apply ha i
    funext j
    rw [Subsingleton.elim j 0, h]
    rfl
  have hdot : ∀ (v w : Fin 1 → ℝ), v ⬝ᵥ w = v 0 * w 0 := by
    intro v w
    simp [dotProduct]
  set c : Fin n → ℝ := fun i => b i / a i 0 with hc
  obtain ⟨m, hm1, hm2⟩ := aux_oqh_median n c
  let fLt : Fin n → Option Ordering := fun i =>
    if m ≤ c i then some (if 0 < a i 0 then Ordering.lt else Ordering.gt) else none
  let fEq : Fin n → Option Ordering := fun i =>
    some (compare (a i 0 * m) (b i))
  let fGt : Fin n → Option Ordering := fun i =>
    if c i ≤ m then some (if 0 < a i 0 then Ordering.gt else Ordering.lt) else none
  refine ⟨QTree.query (fun _ => 1) m (QTree.leaf fLt) (QTree.leaf fEq) (QTree.leaf fGt), ?_⟩
  intro x
  have hx : (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ x = x 0 := by rw [hdot]; ring
  rcases lt_trichotomy (x 0) m with h | h | h
  · have hcmp : compare ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ x) m = Ordering.lt := by
      rw [hx]; exact compare_lt_iff_lt.2 h
    simp only [QTree.eval, QTree.numQueries, hcmp]
    refine ⟨le_refl _, ?_, ?_⟩
    · intro i o hio
      simp only [fLt] at hio
      split_ifs at hio with h1 h2
      · cases hio
        rw [hdot]
        apply compare_lt_iff_lt.2
        have hx' : x 0 < b i / a i 0 := lt_of_lt_of_le h h1
        have := (lt_div_iff₀ h2).1 hx'
        linarith
      · cases hio
        rw [hdot]
        apply compare_gt_iff_gt.2
        have hneg : a i 0 < 0 := lt_of_le_of_ne (not_lt.1 h2) (ha0 i)
        have hx' : x 0 < b i / a i 0 := lt_of_lt_of_le h h1
        have := (lt_div_iff_of_neg hneg).1 hx'
        linarith
    · have : (Finset.univ.filter fun i => (fLt i).isSome) =
          Finset.univ.filter fun i => m ≤ c i := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, fLt]
        split_ifs with h1 <;> simp [h1]
      rw [this]; exact hm1
  · have hcmp : compare ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ x) m = Ordering.eq := by
      rw [hx]; exact compare_eq_iff_eq.2 h
    simp only [QTree.eval, QTree.numQueries, hcmp]
    refine ⟨le_refl _, ?_, ?_⟩
    · intro i o hio
      simp only [fEq, Option.some.injEq] at hio
      rw [hdot, h, hio]
    · have : (Finset.univ.filter fun i => (fEq i).isSome) = Finset.univ := by
        ext i; simp [fEq]
      rw [this, Finset.card_univ, Fintype.card_fin]
      omega
  · have hcmp : compare ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ x) m = Ordering.gt := by
      rw [hx]; exact compare_gt_iff_gt.2 h
    simp only [QTree.eval, QTree.numQueries, hcmp]
    refine ⟨le_refl _, ?_, ?_⟩
    · intro i o hio
      simp only [fGt] at hio
      split_ifs at hio with h1 h2
      · cases hio
        rw [hdot]
        apply compare_gt_iff_gt.2
        have hx' : b i / a i 0 < x 0 := lt_of_le_of_lt h1 h
        have := (div_lt_iff₀ h2).1 hx'
        linarith
      · cases hio
        rw [hdot]
        apply compare_lt_iff_lt.2
        have hneg : a i 0 < 0 := lt_of_le_of_ne (not_lt.1 h2) (ha0 i)
        have hx' : b i / a i 0 < x 0 := lt_of_le_of_lt h1 h
        have := (div_lt_iff_of_neg hneg).1 hx'
        linarith
    · have : (Finset.univ.filter fun i => (fGt i).isSome) =
          Finset.univ.filter fun i => c i ≤ m := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, fGt]
        split_ifs with h1 <;> simp [h1]
      rw [this]; exact hm2
