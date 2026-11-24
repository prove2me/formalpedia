-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_swap_count_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:52:27.944378+00:00
-- url     : https://prove2.me/submissions/2c7ec840-be25-47e8-bed9-cdfdb63fe920

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_two_fibre_count_transitions
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_survivor_singleton_profile
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fibre_counts
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
    S9SwapCountShape
      (Finset.univ \ representativeSet rep)
      (fun i => finiteModelEquiv (S i : G))
      (finiteModelEquiv (S (rep j) : G))
      (finiteModelEquiv (S y : G)) := by
  classical
  let f : Fin 24 → F3T := fun i => finiteModelEquiv (S i : G)
  let A : Finset (Fin 24) := Finset.univ \ representativeSet rep
  let A' : Finset (Fin 24) :=
    Finset.univ \ representativeSet (Function.update rep j y)
  let a : F3T := f (rep j)
  let b : F3T := f y
  let p : ℕ := (A.filter (fun i => f i = a)).card
  let q : ℕ := (A.filter (fun i => f i = b)).card
  have hab : a ≠ b := by
    intro heq
    apply hVal
    apply Subtype.ext
    exact finiteModelEquiv.injective heq
  have hxy : rep j ≠ y := by
    intro heq
    apply hVal
    rw [heq]
  have hRep' :
      ∀ k, (Function.update rep j y) k ∈ c.blocks k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using hy
    · simpa [Function.update, hkj] using hRep k
  obtain ⟨u, _hOne, hBound, hUnique, _hSum⟩ :=
    s9_certificate_survivor_singleton_profile c hs rep hRep
  obtain ⟨u', _hOne', hBound', hUnique', _hSum'⟩ :=
    s9_certificate_survivor_singleton_profile c hs
      (Function.update rep j y) hRep'
  have hBnd : ∀ v, (A.filter (fun i => f i = v)).card ≤ 2 := by
    intro v
    simpa [A, f] using hBound v
  have hBnd' : ∀ v, (A'.filter (fun i => f i = v)).card ≤ 2 := by
    intro v
    simpa [A', f] using hBound' v
  have hUn : ∀ v,
      (A.filter (fun i => f i = v)).card = 1 → v = u := by
    intro v hv
    exact hUnique v (by simpa [A, f] using hv)
  have hUn' : ∀ v,
      (A'.filter (fun i => f i = v)).card = 1 → v = u' := by
    intro v hv
    exact hUnique' v (by simpa [A', f] using hv)
  have hCountA :
      (A'.filter (fun i => f i = a)).card = p + 1 := by
    have h := s9_certificate_swap_fibre_counts
      c rep hRep j hy hxy a
    change (A'.filter (fun i => f i = a)).card +
        (if b = a then 1 else 0) =
      p + (if a = a then 1 else 0) at h
    simpa [hab.symm] using h
  have hCountB :
      (A'.filter (fun i => f i = b)).card + 1 = q := by
    have h := s9_certificate_swap_fibre_counts
      c rep hRep j hy hxy b
    change (A'.filter (fun i => f i = b)).card +
        (if b = b then 1 else 0) =
      q + (if a = b then 1 else 0) at h
    simpa [hab] using h
  have hp : p + 1 ≤ 2 := by
    have h := hBnd' a
    omega
  have hq : 1 ≤ q := by omega
  have hq2 : q ≤ 2 := hBnd b
  have hBefore : p = 1 → q ≠ 1 := by
    intro hp1 hq1
    apply hab
    exact (hUn a (by simpa [p] using hp1)).trans
      (hUn b (by simpa [q] using hq1)).symm
  have hAfter : p + 1 = 1 → q - 1 ≠ 1 := by
    intro hp1 hq1
    apply hab
    have haOne : (A'.filter (fun i => f i = a)).card = 1 := by
      omega
    have hbOne : (A'.filter (fun i => f i = b)).card = 1 := by
      omega
    exact (hUn' a haOne).trans (hUn' b hbOne).symm
  have hCases :=
    s9_two_fibre_count_transitions p q hp hq hq2 hBefore hAfter
  change (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 2)
  exact hCases
end InverseZeroSum.Candidate3
