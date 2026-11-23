-- Prove2me | solution 1 for GlobalTheory.FinWeil.sumOp_eq_sum_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:17.129182+00:00
-- url     : https://prove2.me/submissions/0c53ed57-a37b-4696-8f2c-ba0e1f9cccc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comp_of_mem

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
private lemma heis_apply_eq_of_sub_mem_of_fixes {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : y - x ∈ A) : W y v = W x v := by
  have hyx : y - x ∈ B := B.sub_mem hy hx
  calc W y v = W (x + (y - x)) v := by rw [add_sub_cancel]
    _ = W x (W (y - x) v) := (h.comp_of_mem hB hx hyx v).symm
    _ = W x v := by rw [hv _ hxy]
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
theorem _root_.solution {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (A B : Submodule R X) (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) (v : M)
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) (ι : Type) [Fintype ι] (f : ι → X)
    (hf : ∀ i, f i ∈ B) (ht : ∀ b ∈ B, ∃! i, b - f i ∈ A) :
    _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
      _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι := by
  let φ : ι → B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    fun i => ((⟨f i, hf i⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have hji : f j - f i ∈ A := (quotient_mk_eq_mk_iff_sub_mem A B _ _).1 hij
      obtain ⟨k, -, hk⟩ := ht (f j) (hf j)
      rw [hk i hji, hk j (by simp)]
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H b =>
        obtain ⟨i, hi, -⟩ := ht b b.2
        exact ⟨i, (quotient_mk_eq_mk_iff_sub_mem A B _ _).2 hi⟩
  let e := Equiv.ofBijective φ hφ
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact heis_apply_eq_of_sub_mem_of_fixes h hB hv (hf i) (Quotient.out (e i)).2
      (quotient_out_sub_mem A B (e i) ⟨f i, hf i⟩ rfl)
  · unfold _root_.GlobalTheory.FinWeil.idx
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr e, Nat.card_eq_fintype_card]
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
