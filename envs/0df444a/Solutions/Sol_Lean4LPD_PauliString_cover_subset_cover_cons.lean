-- Prove2me | solution 1 for Lean4LPD.PauliString.cover_subset_cover_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:04.419022+00:00
-- url     : https://prove2.me/submissions/c2d33d4c-dfc3-4cd9-87a6-59969afa7b5a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_mem_hitting
public import Theorems.Thm_Lean4LPD_PauliString_subset_cover
public import Theorems.Thm_Lean4LPD_PauliString_support_subset_cover_of_mem_hitting

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution {G : PauliString n} {Gs : List (PauliString n)}
    (hG : ∀ H ∈ Gs, Disjoint (support G) (support H))
    (hGS : (support G ∩ S).Nonempty) (hT : T ⊆ S ∪ support G) :
    cover Gs T ⊆ cover (G :: Gs) S := by
  have hGmem : G ∈ hitting (G :: Gs) S :=
    mem_hitting.2 ⟨List.mem_cons_self, hGS⟩
  have hGcover : support G ⊆ cover (G :: Gs) S := support_subset_cover_of_mem_hitting hGmem
  have hhit : hitting Gs T ⊆ hitting (G :: Gs) S := by
    intro H hH
    rw [mem_hitting] at hH ⊢
    obtain ⟨i, hi⟩ := hH.2
    rw [Finset.mem_inter] at hi
    refine ⟨List.mem_cons_of_mem _ hH.1, ⟨i, Finset.mem_inter.2 ⟨hi.1, ?_⟩⟩⟩
    rcases Finset.mem_union.1 (hT hi.2) with hiS | hiG
    · exact hiS
    · exact absurd hi.1 (Finset.disjoint_left.1 (hG H hH.1) hiG)
  refine Finset.union_subset (hT.trans (Finset.union_subset (subset_cover _ _) hGcover)) ?_
  exact (Finset.biUnion_subset_biUnion_of_subset_left _ hhit).trans Finset.subset_union_right
end Lean4LPD.PauliString
