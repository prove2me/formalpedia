-- Prove2me | solution 1 for HallReps.CDR.card_lt_of_subset_cdrMeet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:58.597716+00:00
-- url     : https://prove2.me/submissions/3af59b22-e42d-46a4-840c-d083d862c92f

import Mathlib
import Definitions.Def_HallReps_CDR_System
import Theorems.Thm_HallReps_CDR_lemma_cdrMeet

set_option autoImplicit false

open HallReps.CDR

theorem solution {α : Type*} {m : ℕ} (T : Fin (m + 1) → Set α)
    (b : Fin m → α) (hb : IsCDR (fun i : Fin m => T i.castSucc) b)
    (hT : T (Fin.last m) ⊆ cdrMeet (fun i : Fin m => T i.castSucc)) :
    ∃ s : Finset (Fin (m + 1)), Fin.last m ∈ s ∧
      (⋃ i ∈ s, T i) = cdrMeet (fun i : Fin m => T i.castSucc) ∧
      (cdrMeet (fun i : Fin m => T i.castSucc)).Finite ∧
      s.card = (cdrMeet (fun i : Fin m => T i.castSucc)).ncard + 1 := by
  classical
  set R := cdrMeet (fun i : Fin m => T i.castSucc) with hR
  obtain ⟨hunion, hcard⟩ := HallReps.CDR.lemma_cdrMeet (fun i : Fin m => T i.castSucc) b hb
  -- indices of the first `m` sets represented by elements of `R`
  let IR : Finset (Fin m) := Finset.univ.filter (fun i => b i ∈ R)
  have hIRcard : (R.encard) = (IR.card : ℕ∞) := by
    rw [hcard]
    have : ENat.card {i : Fin m // b i ∈ R} = (IR.card : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, ← ENat.card_coe_set_eq]
      apply ENat.card_congr
      exact Equiv.subtypeEquivRight (by intro i; simp [IR])
    exact this
  have hRfin : R.Finite := Set.finite_of_encard_le_coe (le_of_eq hIRcard)
  refine ⟨insert (Fin.last m) (IR.map Fin.castSuccEmb), Finset.mem_insert_self _ _, ?_, hRfin, ?_⟩
  · -- the union of these sets is `R`
    have hU : (⋃ i ∈ insert (Fin.last m) (IR.map Fin.castSuccEmb), T i) =
        T (Fin.last m) ∪ ⋃ i ∈ IR, T i.castSucc := by
      ext x
      simp only [Finset.mem_insert, Set.mem_iUnion, Finset.mem_map, Fin.coe_castSuccEmb,
        exists_prop, Set.mem_union]
      constructor
      · rintro ⟨i, hi | ⟨j, hj, rfl⟩, hx⟩
        · subst hi; exact Or.inl hx
        · exact Or.inr ⟨j, hj, hx⟩
      · rintro (hx | ⟨j, hj, hx⟩)
        · exact ⟨Fin.last m, Or.inl rfl, hx⟩
        · exact ⟨j.castSucc, Or.inr ⟨j, hj, rfl⟩, hx⟩
    have hIR : (⋃ i ∈ IR, T i.castSucc) = R := by
      refine Eq.trans ?_ hunion
      ext x
      simp only [IR, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
      exact Iff.rfl
    rw [hU, hIR]
    exact Set.union_eq_self_of_subset_left hT
  · -- the cardinality
    have hlast : Fin.last m ∉ IR.map Fin.castSuccEmb := by
      simp [Finset.mem_map, Fin.castSucc_ne_last]
    rw [Finset.card_insert_of_notMem hlast, Finset.card_map]
    have : R.ncard = IR.card := by
      have h1 : (R.ncard : ℕ∞) = R.encard := hRfin.cast_ncard_eq
      rw [hIRcard] at h1
      exact_mod_cast h1
    rw [this]

#print axioms solution
