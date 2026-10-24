-- Prove2me | solution 1 for MICPRep.Periodic.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:52:30.522693+00:00
-- url     : https://prove2.me/submissions/ea1cb27b-b977-4e4d-b4f2-9fa1821129fd

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_lemma_6_2
import Theorems.Thm_MICPRep_Periodic_proposition_5_3_union
import Theorems.Thm_MICPRep_Periodic_lemma_6_1

/- Complete local bodies from DecompositionStatement.lean. -/

open MICPRep.Periodic
open scoped ENNReal Matrix

set_option linter.unusedVariables false in
def DecompositionStatement : Prop :=
  ∀ {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty),
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (Ms : Fin k → Set (Ambient n p d)) (Ss : Fin k → Set (Pt n)),
        (∀ i, IsRationalFormulation (Ms i) (Ss i) ∧ (Ss i).Nonempty) ∧
        S = S₀ ∪ ⋃ i, Ss i ∧
        ∀ i, micpDiam (Ms i) ≤ micpDiam M ∧
          (intrinsicInterior ℝ (IZ (indexSet (Ms i))) ∩ intLattice d).Nonempty

/- Complete local bodies from FiniteCover.lean. -/

namespace MICPRep.Periodic.CoverProof

def HasCover {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
    ∃ (k : ℕ) (T : Fin k → Set (Pt n)),
      (∀ i, HasNearlyPeriodicFormulation (T i)) ∧
      S ⊆ S₀ ∪ ⋃ i, T i ∧ S₀ ∪ ⋃ i, T i ⊆ closure S

lemma binary_empty (n : ℕ) : IsBinaryMICPR (∅ : Set (Pt n)) := by
  have h := MICPRep.Periodic.proposition_5_3_union (fun _ : Fin 0 => (∅ : Set (Pt n)))
    (fun i => Fin.elim0 i)
  simpa using h

lemma binary_cover {n : ℕ} {S : Set (Pt n)} (hS : IsBinaryMICPR S) : HasCover S := by
  refine ⟨S, hS, 0, fun _ => ∅, fun i => Fin.elim0 i, ?_, ?_⟩
  · simp
  · simpa using (subset_closure : S ⊆ closure S)

lemma near_cover {n : ℕ} {S : Set (Pt n)} (hS : HasNearlyPeriodicFormulation S) : HasCover S := by
  refine ⟨∅, binary_empty n, 1, fun _ => S, fun _ => hS, ?_, ?_⟩
  · intro x hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨0, hx⟩)
  · intro x hx
    rcases hx with hx | hx
    · exact False.elim hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact subset_closure hi

lemma transfer_cover {n : ℕ} {S T : Set (Pt n)} (hT : HasCover T)
    (hST : S ⊆ T) (hcl : closure T ⊆ closure S) : HasCover S := by
  obtain ⟨B, hB, k, U, hU, hsub, hsup⟩ := hT
  exact ⟨B, hB, k, U, hU, hST.trans hsub, hsup.trans hcl⟩

lemma merge_covers {n k : ℕ} (S B : Set (Pt n)) (Ss : Fin k → Set (Pt n))
    (hB : IsBinaryMICPR B) (hS : S = B ∪ ⋃ i, Ss i) (hcover : ∀ i, HasCover (Ss i)) :
    HasCover S := by
  classical
  choose Bs hBs ks Ts hTs hsubs hsups using hcover
  let C : Fin (k + 1) → Set (Pt n) := Fin.cons B Bs
  have hC : IsBinaryMICPR (⋃ i, C i) := by
    apply MICPRep.Periodic.proposition_5_3_union
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hB
    · exact hBs j
  let J := Σ i : Fin k, Fin (ks i)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let U : Fin (Fintype.card J) → Set (Pt n) := fun j => Ts (e.symm j).1 (e.symm j).2
  refine ⟨⋃ i, C i, hC, Fintype.card J, U, ?_, ?_, ?_⟩
  · intro j
    exact hTs (e.symm j).1 (e.symm j).2
  · intro x hx
    rw [hS] at hx
    rcases hx with hx | hx
    · exact Or.inl (Set.mem_iUnion.mpr ⟨0, hx⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rcases hsubs i hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i.succ, hi⟩)
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
        apply Or.inr
        apply Set.mem_iUnion.mpr ⟨e ⟨i, j⟩, ?_⟩
        change x ∈ (fun a : J => Ts a.1 a.2) (e.symm (e ⟨i, j⟩))
        rw [e.symm_apply_apply]
        exact hj
  · have hBsub : B ⊆ S := by rw [hS]; exact Set.subset_union_left
    have hSisub (i : Fin k) : Ss i ⊆ S := by
      rw [hS]
      exact (Set.subset_iUnion Ss i).trans Set.subset_union_right
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        exact subset_closure (hBsub hi)
      · intro hi
        exact closure_mono (hSisub j) (hsups j (Or.inl hi))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact closure_mono (hSisub (e.symm i).1)
        (hsups (e.symm i).1 (Or.inr (Set.mem_iUnion.mpr ⟨(e.symm i).2, hi⟩)))

end MICPRep.Periodic.CoverProof

/- Complete local bodies from Assembly.lean. -/

open MICPRep.Periodic MICPRep.Periodic.CoverProof
open scoped ENNReal Matrix

theorem conditional_solution (hdecomp : DecompositionStatement)
    {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (T : Fin k → Set (Pt n)),
        (∀ i, HasNearlyPeriodicFormulation (T i)) ∧
        S ⊆ S₀ ∪ ⋃ i, T i ∧ S₀ ∪ ⋃ i, T i ⊆ closure S := by
  change HasCover S
  induction d using Nat.strong_induction_on generalizing p S with
  | h d ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨B, hB, k, Ms, Ss, hMs, heq, hgood⟩ := hdecomp M S hM hS
        apply merge_covers S B Ss hB heq
        intro i
        have hDi : micpDiam (Ms i) < ⊤ := (hgood i).1.trans_lt hD
        rcases MICPRep.Periodic.lemma_6_2 (Ms i) (Ss i) (hMs i).1 (hMs i).2 hDi (hgood i).2 with
          hbin | hnear | ⟨d', hdim, p', Mt, St, hMt, _, hDt, hsub, _, hclosure⟩
        · exact binary_cover hbin
        · exact near_cover hnear
        · apply transfer_cover (ih d' (by omega) Mt St hMt (hDt.trans_lt hDi)) hsub hclosure
      · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
        rw [hSempty]
        exact binary_cover (binary_empty n)

theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (T : Fin k → Set (Pt n)),
        (∀ i, HasNearlyPeriodicFormulation (T i)) ∧
        S ⊆ S₀ ∪ ⋃ i, T i ∧ S₀ ∪ ⋃ i, T i ⊆ closure S := by
  have hdecomp : DecompositionStatement := @MICPRep.Periodic.lemma_6_1
  exact conditional_solution hdecomp M S hM hD
