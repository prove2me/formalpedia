-- Prove2me | solution 1 for GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:20.045166+00:00
-- url     : https://prove2.me/submissions/aeebc80d-d65f-4d59-82e3-83445fd037c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
namespace GlobalTheory.FinWeil
section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_mk_eq_mk_iff_sub_mem (A B : Submodule R X) (x y : B.toAddSubgroup) :
    ((x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = y) ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [neg_add_eq_sub]
open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_out_sub_mem (A B : Submodule R X)
    (q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) (x : B.toAddSubgroup)
    (hq : (x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = q) :
    ((Quotient.out q : B.toAddSubgroup) : X) - x ∈ A := by
  rw [← quotient_mk_eq_mk_iff_sub_mem, hq]
  exact (QuotientAddGroup.out_eq' q).symm
end
end GlobalTheory.FinWeil
end
end

set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.FinWeil
namespace _root_.GlobalTheory.FinWeil
theorem _root_.solution (A B : Submodule R X)
    (hi : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A := by
  unfold _root_.GlobalTheory.FinWeil.idx at hi
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hi
  haveI := Nat.finite_of_card_ne_zero hi
  let e := Finite.equivFin (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  refine ⟨_, fun i => ((Quotient.out (e.symm i) : B.toAddSubgroup) : X),
    fun i => (Quotient.out (e.symm i) : B.toAddSubgroup).2, ?_⟩
  intro b hb
  refine ⟨e (⟨b, hb⟩ : B.toAddSubgroup), ?_, fun j hj => ?_⟩
  · have := quotient_out_sub_mem A B (e.symm (e (⟨b, hb⟩ : B.toAddSubgroup))) ⟨b, hb⟩ (by simp)
    simpa using A.neg_mem this
  · have h1 : ((⟨b, hb⟩ : B.toAddSubgroup) :
        B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = e.symm j := by
      rw [← QuotientAddGroup.out_eq' (e.symm j), quotient_mk_eq_mk_iff_sub_mem]
      simpa using A.neg_mem hj
    rw [h1, Equiv.apply_symm_apply]
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
