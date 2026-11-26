-- Prove2me | solution 1 for Kyprianou.Ch05.reflectedGridPartitionData
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:50:39.290473+00:00
-- url     : https://prove2.me/submissions/cfeb0adf-a38a-4b4f-81f6-6c66389fd03d

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_nonnegativeHalfOpenGridPartition
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Reflected half-open uniform grid partitions the clipped nonnegative interval. -/
theorem solution
    (x d : Real) (hx : 0 ≤ x) (hd : 0 < d) :
    let S := fun k : Nat => Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d)
    (⋃ k, S k) = Set.Icc 0 x ∧
      Pairwise (Function.onFun Disjoint S) ∧
      (∀ k : Nat, MeasurableSet (S k)) ∧
      (∃ N : Nat, ∀ k : Nat, N ≤ k → S k = ∅) := by
  dsimp only
  let S := fun k : Nat => Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d)
  have hmem (z : Real) (k : Nat) :
      z ∈ S k ↔ z ∈ Icc 0 x ∧
        x-z ∈ Ico ((k : Real)*d) (((k : Real)+1)*d) := by
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor
    · rintro ⟨hz,hl,hu⟩
      exact ⟨hz,by linarith,by linarith⟩
    · rintro ⟨hz,hl,hu⟩
      exact ⟨hz,by linarith,by linarith⟩
  obtain ⟨hU,hD⟩ := nonnegativeHalfOpenGridPartition d hd
  refine ⟨?_,?_,fun k => measurableSet_Icc.inter measurableSet_Ioc,?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨k,hk⟩ := mem_iUnion.mp hz
      exact (hmem z k).mp hk |>.1
    · intro hz
      have hz' : x-z ∈ Ici (0 : Real) := sub_nonneg.mpr hz.2
      rw [← hU] at hz'
      obtain ⟨k,hk⟩ := mem_iUnion.mp hz'
      exact mem_iUnion.mpr ⟨k,(hmem z k).mpr ⟨hz,hk⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact (Set.disjoint_left.mp (hD hij)) ((hmem z i).mp hi).2 ((hmem z j).mp hj).2
  · refine ⟨Nat.floor (x/d)+1,?_⟩
    intro k hk
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hlt : x/d < (Nat.floor (x/d) : Real)+1 := Nat.lt_floor_add_one _
    have hcast : (Nat.floor (x/d) : Real)+1 ≤ (k : Real) := by exact_mod_cast hk
    have h := (hmem z k).mp hz
    have hmul : x < (k : Real)*d := (div_lt_iff₀ hd).mp (hlt.trans_le hcast)
    linarith [h.1.1,h.2.1]
