-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_representative_sum_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:52:28.464795+00:00
-- url     : https://prove2.me/submissions/87fb60b3-8149-43fb-b6aa-8a718b370255

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_survivor_singleton_profile
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
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j) :
    ∃ u : F3T,
      (((Finset.univ \ representativeSet rep).filter
        (fun i => finiteModelEquiv (S i : G) = u)).card = 1) ∧
      (∀ v : F3T,
        ((Finset.univ \ representativeSet rep).filter
          (fun i => finiteModelEquiv (S i : G) = v)).card = 1 → v = u) ∧
      (∑ j : Fin c.s, finiteModelEquiv (S (rep j) : G)) =
        (∑ i : Fin 24, finiteModelEquiv (S i : G)) + u := by
  classical
  obtain ⟨u, hOne, _hBound, hUnique, hSum⟩ :=
    s9_certificate_survivor_singleton_profile c hs rep hRep
  let f : Fin 24 → F3T := fun i => finiteModelEquiv (S i : G)
  have hInj : Function.Injective rep := by
    intro i j hij
    by_contra hne
    have hDis := c.pairwise_disjoint i j hne
    have hj : rep i ∈ c.blocks j := by
      rw [hij]
      exact hRep j
    exact (Finset.disjoint_left.mp hDis) (hRep i) hj
  have hSelected :
      (∑ i ∈ representativeSet rep, f i) =
        ∑ j : Fin c.s, f (rep j) := by
    unfold representativeSet
    rw [Finset.sum_image]
    intro i _hi j _hj hij
    exact hInj hij
  have hSplit :
      (∑ j : Fin c.s, f (rep j)) +
        (∑ i ∈ (Finset.univ \ representativeSet rep), f i) =
      ∑ i : Fin 24, f i := by
    rw [← hSelected]
    simpa [add_comm] using
      (Finset.sum_sdiff
        (Finset.subset_univ (representativeSet rep)) (f := f))
  have hSum' :
      (∑ i ∈ (Finset.univ \ representativeSet rep), f i) + u = 0 := by
    simpa [f] using hSum
  have hEquation :
      (∑ j : Fin c.s, f (rep j)) =
        (∑ i : Fin 24, f i) + u := by
    calc
      (∑ j : Fin c.s, f (rep j)) =
          (∑ j : Fin c.s, f (rep j)) +
            ((∑ i ∈ (Finset.univ \ representativeSet rep), f i) + u) := by
              rw [hSum']
              simp
      _ = ((∑ j : Fin c.s, f (rep j)) +
            (∑ i ∈ (Finset.univ \ representativeSet rep), f i)) + u := by
              abel
      _ = (∑ i : Fin 24, f i) + u := by rw [hSplit]
  exact ⟨u, hOne, hUnique, by simpa [f] using hEquation⟩
end InverseZeroSum.Candidate3
