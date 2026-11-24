-- Prove2me | solution 2 for InverseZeroSum.Candidate3.tupleValueT_sum_eq_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:21.879888+00:00
-- url     : https://prove2.me/submissions/aa8a4180-5564-4af4-97e9-c3b222881f27

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
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
theorem _root_.solution {n : ℕ} (R : PosSeq n) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)), tupleValueT R i) =
      ∑ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => tupleValueT R i = x)).card • x := by
  classical
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        tupleValueT R i ∈ tupleSupportT R := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hFiberwise :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin n))) (t := tupleSupportT R)
      (g := tupleValueT R) hMaps (tupleValueT R)
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin n)), tupleValueT R i) =
        ∑ x ∈ tupleSupportT R,
          ∑ i ∈ (Finset.univ : Finset (Fin n)) with
            tupleValueT R i = x, tupleValueT R i := by
              simpa using hFiberwise.symm
    _ =
        ∑ x ∈ tupleSupportT R,
          ((Finset.univ : Finset (Fin n)).filter
            (fun i => tupleValueT R i = x)).card • x := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ i ∈ (Finset.univ : Finset (Fin n)) with
            tupleValueT R i = x, tupleValueT R i) =
            ∑ _i ∈ (Finset.univ : Finset (Fin n)).filter
              (fun i => tupleValueT R i = x), x := by
                exact Finset.sum_congr rfl
                  (fun i hi => (Finset.mem_filter.mp hi).2)
        _ =
            ((Finset.univ : Finset (Fin n)).filter
              (fun i => tupleValueT R i = x)).card • x := by
                simp
end InverseZeroSum.Candidate3
