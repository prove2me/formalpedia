-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleFiberT_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:17.52499+00:00
-- url     : https://prove2.me/submissions/99904f6b-149f-4b8c-931c-b0e8aea88055

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_three_nsmul_G
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (R : PosSeq n) (hFree : ShortFree R) :
    ∀ x ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin n)).filter
        (fun i => tupleValueT R i = x)).card ≤ 2 := by
  classical
  intro x _hx
  let fiber : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => tupleValueT R i = x)
  have hfiber_eq :
      fiber =
        (Finset.univ : Finset (Fin n)).filter
          (fun i => tupleValueT R i = x) := rfl
  rw [← hfiber_eq]
  by_contra hle
  have h3 : 3 ≤ fiber.card := by omega
  obtain ⟨I, hI_sub, hIcard⟩ :=
    Finset.exists_subset_card_eq (s := fiber) (n := 3) h3
  have hconst :
      ∀ i ∈ I, (R i : G) = finiteModelEquiv.symm x := by
    intro i hi
    have hiFiber : i ∈ fiber := hI_sub hi
    have hfix : tupleValueT R i = x := (Finset.mem_filter.mp hiFiber).2
    have hback := congrArg finiteModelEquiv.symm hfix
    simpa [tupleValueT] using hback
  have hsum : posSum R I = 0 := by
    unfold posSum
    calc
      (∑ i ∈ I, (R i : G)) =
          ∑ _i ∈ I, finiteModelEquiv.symm x := by
            exact Finset.sum_congr rfl (fun i hi => hconst i hi)
      _ = I.card • finiteModelEquiv.symm x := by simp
      _ = 0 := by
        rw [hIcard]
        simpa using
          three_nsmul_G (finiteModelEquiv.symm x)
  exact (hFree I) ⟨Finset.card_pos.mp (by omega), by omega, hsum⟩
end InverseZeroSum.Candidate3
