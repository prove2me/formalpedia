-- Prove2me | solution 1 for OAI.Problem310.ScaleDiscretization.exists_monotone_representatives
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:28:52.119496+00:00
-- url     : https://prove2.me/submissions/61947c05-d392-4b4f-af84-561be88982cb

-- Adapted from OpenAI/math contributors, MonotoneRepresentatives.lean lines 13–63,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-- Alexander Richard Towell (queelius) directed the contribution; Codex adapted
-- and verified the proof. The mathematical construction is credited upstream.
import Mathlib
universe u_α u_ι
open scoped BigOperators

/-- On a chain of integer vectors, the sum of the coordinates determines the vector. -/
private lemma vector_eq_of_sum_eq {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    {s : Set α} {f : α → ι → ℤ} (hf : MonotoneOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hs : (∑ i, f x i) = ∑ i, f y i) : f x = f y := by
  classical
  rcases le_total x y with hxy | hyx
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hf hx hy hxy i)).mp hs i
      (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hf hy hx hyx i)).mp hs.symm i
      (Finset.mem_univ i)).symm

/-- A monotone family of finitely many integer-valued functions has a small common
representative set. Unlike a breakpoint construction, this also handles every boundary
value without a separate endpoint convention. -/
theorem solution {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    (a b : α) (hab : a ≤ b) (f : α → ι → ℤ)
    (hf : MonotoneOn f (Set.Icc a b)) :
    ∃ R : Finset α,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ ((∑ i, f b i) + 1 - ∑ i, f a i).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R, f t' = f t := by
  classical
  let rank : α → ℤ := fun t => ∑ i, f t i
  let rep : ℤ → α := fun k =>
    if h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k then Classical.choose h else a
  have rep_mem (k : ℤ) : rep k ∈ Set.Icc a b := by
    dsimp [rep]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ⟨le_rfl, hab⟩
  have rep_rank {k : ℤ} (h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k) :
      rank (rep k) = k := by
    dsimp [rep]
    rw [dif_pos h]
    exact (Classical.choose_spec h).2
  refine ⟨(Finset.Icc (rank a) (rank b)).image rep, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact rep_mem k
  · exact (Finset.card_image_le).trans_eq (Int.card_Icc _ _)
  · intro t ht
    have hlow : rank a ≤ rank t := by
      exact Finset.sum_le_sum fun i _ => hf ⟨le_rfl, hab⟩ ht ht.1 i
    have hhigh : rank t ≤ rank b := by
      exact Finset.sum_le_sum fun i _ => hf ht ⟨hab, le_rfl⟩ ht.2 i
    refine ⟨rep (rank t), Finset.mem_image.mpr ⟨rank t, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
    · exact vector_eq_of_sum_eq hf (rep_mem _) ht (rep_rank ⟨t, ht, rfl⟩)
