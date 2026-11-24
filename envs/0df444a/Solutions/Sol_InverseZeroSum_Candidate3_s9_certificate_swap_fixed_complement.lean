-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:23.85087+00:00
-- url     : https://prove2.me/submissions/5364e7b8-8f7c-4803-9a0f-d83617d2308e

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fibre_counts
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_count_cases
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_representative_sum_profile
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24} (hy : y ∈ c.blocks j)
    (hVal : S (rep j) ≠ S y) :
    (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
      finiteModelEquiv (S (rep k) : G)) =
    ∑ i : Fin 24, finiteModelEquiv (S i : G) := by
  classical
  let f : Fin 24 → F3T := fun i => finiteModelEquiv (S i : G)
  let A : Finset (Fin 24) := Finset.univ \ representativeSet rep
  let rep' : Fin c.s → Fin 24 := Function.update rep j y
  let A' : Finset (Fin 24) := Finset.univ \ representativeSet rep'
  let a : F3T := f (rep j)
  let b : F3T := f y
  let p : ℕ := (A.filter (fun i => f i = a)).card
  let q : ℕ := (A.filter (fun i => f i = b)).card
  let t : F3T :=
    ∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j, f (rep k)
  let T : F3T := ∑ i : Fin 24, f i
  have hab : a ≠ b := by
    intro heq
    apply hVal
    apply Subtype.ext
    exact finiteModelEquiv.injective heq
  have hxy : rep j ≠ y := by
    intro h
    apply hVal
    rw [h]
  have hRep' : ∀ k, rep' k ∈ c.blocks k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [rep'] using hy
    · simpa [rep', Function.update, hkj] using hRep k
  obtain ⟨u, _hOne, hUnique, hSelect⟩ :=
    s9_certificate_representative_sum_profile c hs rep hRep
  obtain ⟨u', _hOne', hUnique', hSelect'⟩ :=
    s9_certificate_representative_sum_profile c hs rep' hRep'
  have hSelectOld :
      (∑ k : Fin c.s, f (rep k)) = T + u := by
    simpa [f, T] using hSelect
  have hSelectNew :
      (∑ k : Fin c.s, f (rep' k)) = T + u' := by
    simpa [f, T, rep'] using hSelect'
  have hOldSplit :
      (∑ k : Fin c.s, f (rep k)) = t + a := by
    simpa [t, a] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin c.s))
        (fun k => f (rep k)) (Finset.mem_univ j)).symm
  have hOther :
      (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
          f (rep' k)) = t := by
    unfold t
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [rep', Function.update, hkj]
  have hNewSplit :
      (∑ k : Fin c.s, f (rep' k)) = t + b := by
    calc
      _ = (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
            f (rep' k)) + f (rep' j) :=
        (Finset.sum_erase_add (Finset.univ : Finset (Fin c.s))
          (fun k => f (rep' k)) (Finset.mem_univ j)).symm
      _ = t + b := by rw [hOther]; simp [rep', b]
  have hCases :=
    s9_certificate_swap_count_cases c hs rep hRep j hy hVal
  change (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 2) at hCases
  rcases hCases with h01 | h12
  · have hOldSingleton : u = b := by
      have hb : b = u := hUnique b (by simpa [A, f, q] using h01.2)
      exact hb.symm
    have hNewACard :
        (A'.filter (fun i => f i = a)).card = 1 := by
      have h := s9_certificate_swap_fibre_counts
        c rep hRep j hy hxy a
      change (A'.filter (fun i => f i = a)).card +
          (if b = a then 1 else 0) =
        p + (if a = a then 1 else 0) at h
      simp [hab.symm] at h
      omega
    have hNewSingleton : u' = a := by
      have ha : a = u' := hUnique' a (by simpa [A', f, rep'] using hNewACard)
      exact ha.symm
    rw [hOldSplit, hOldSingleton] at hSelectOld
    rw [hNewSplit, hNewSingleton] at hSelectNew
    have hDouble : a + a = b + b := by
      calc
        a + a = (t + a) + (T + a) - (t + T) := by abel
        _ = (T + b) + (t + b) - (t + T) := by
          rw [hSelectOld, ← hSelectNew]
        _ = b + b := by abel
    have hDoubleInj : ∀ v w : F3T, v + v = w + w → v = w := by
      decide
    exact (hab (hDoubleInj a b hDouble)).elim
  · have hOldSingleton : u = a := by
      have ha : a = u := hUnique a (by simpa [A, f, p] using h12.1)
      exact ha.symm
    rw [hOldSplit, hOldSingleton] at hSelectOld
    exact add_right_cancel hSelectOld
end InverseZeroSum.Candidate3
