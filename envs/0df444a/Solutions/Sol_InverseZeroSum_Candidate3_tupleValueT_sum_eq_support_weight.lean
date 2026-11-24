-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleValueT_sum_eq_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:34:51.150572+00:00
-- url     : https://prove2.me/submissions/16a968fd-02fb-4243-b145-5b90a5d4639a

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution {n : ℕ} (R : PosSeq n) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)), tupleValueT R i) =
      ∑ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => tupleValueT R i = x)).card • x := by
  classical
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin n)), tupleValueT R i ∈ tupleSupportT R := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hm (tupleValueT R)]
  apply Finset.sum_congr rfl; intro v _
  rw [← Finset.sum_const]; apply Finset.sum_congr rfl; intro i hi
  exact (Finset.mem_filter.mp hi).2
