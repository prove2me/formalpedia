-- Prove2me | solution 1 for GlobalTheory.FinWeil.sumOp_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:12.152094+00:00
-- url     : https://prove2.me/submissions/b620918a-0f85-47e4-aeb3-37ec880b3fa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_eq_sum_transversal
import Theorems.Thm_GlobalTheory_FinWeil_exists_transversal_of_idx_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comp_of_mem
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_comp

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
open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma fixes_sumOp_of_selfDual {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) :
    _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) := by
  intro b hb
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set g : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup → M :=
    fun q => W ((Quotient.out q : B.toAddSubgroup) : X) v with hg
  have hinj : ∀ u : M, W b u = 0 → u = 0 := by
    intro u hu
    have h1 := h.neg_comp b u
    rw [hu, map_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _)
  have hmap : W b (∑ᶠ q, g q) = ∑ᶠ q, W b (g q) := by
    by_cases hs : (Function.support g).Finite
    · exact map_finsum (W b) hs
    · have hs' : ¬ (Function.support fun q => W b (g q)).Finite := by
        refine fun hfin => hs (hfin.subset fun q hq => ?_)
        exact fun h0 => hq (hinj _ h0)
      rw [finsum_of_infinite_support hs, map_zero, finsum_of_infinite_support hs']
  rw [hmap]
  let c : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    ((⟨b, hb⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hterm : ∀ q, W b (g q) = g (c + q) := by
    intro q
    have hq : ((Quotient.out q : B.toAddSubgroup) : X) ∈ B := (Quotient.out q).2
    rw [hg, h.comp_of_mem hB hb hq v]
    refine (heis_apply_eq_of_sub_mem_of_fixes h hB hv (B.add_mem hb hq) (Quotient.out (c + q)).2
      (quotient_out_sub_mem A B (c + q) (⟨b, hb⟩ + Quotient.out q) ?_)).symm
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  simp_rw [hterm]
  exact finsum_comp_equiv (Equiv.addLeft c)
end GlobalTheory.FinWeil
end
end

set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
open Classical
open scoped BigOperators
namespace GlobalTheory.FinWeil
namespace _root_.GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M},
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X),
    _root_.GlobalTheory.FinWeil.SelfDual γ B → (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → ∀ (ι : Type) [Fintype ι]
      (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι) ∧
    (_root_.GlobalTheory.FinWeil.idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧
      ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧
      (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)) ∧
      ∀ (c : ℂ) v, _root_.GlobalTheory.FinWeil.sumOp W A B (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A B v) ∧
    (B ≤ A → _root_.GlobalTheory.FinWeil.idx A B = 1 ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W A B v = v) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hB
  have hunit : ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → B ≤ A →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ _i : Unit, W 0 v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card Unit := fun v hv hBA =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv Unit (fun _ => 0) (fun _ => B.zero_mem)
      (fun b hb => ⟨(), by simpa using hBA hb, fun _ _ => rfl⟩)
  refine ⟨fun v hv ι _ f hf ht => _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv ι f hf ht,
    fun hi => ⟨_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A B hi,
      fun v hv => fixes_sumOp_of_selfDual h hB hv, fun c v => ?_⟩, fun hBA => ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    simp_rw [map_smul]
    exact (smul_finsum c _).symm
  · refine ⟨(hunit 0 (fun a _ => map_zero _) hBA).2.trans (by simp), fun v hv => ?_⟩
    rw [(hunit v hv hBA).1]
    simpa using hv 0 A.zero_mem
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
