-- Prove2me | solution 1 for MatchingLogic.finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:04.429833+00:00
-- url     : https://prove2.me/submissions/9a048022-9460-4633-8e07-8b99c3e44647

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_locConsistent_insert_captureAvoidingWitness
public import Theorems.Thm_MatchingLogic_henkinLimit_locConsistent
public import Theorems.Thm_MatchingLogic_Pattern_allVars_subset_listSupport
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
public import Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_locConsistent_extend_isMCS
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
private theorem Pattern.henkinFresh_not_mem_body
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    henkinFresh l p ∉ p.allVars := by
  intro hmem
  exact (Pattern.imp (listSupport l) p).fresh_not_mem_allVars
    (Finset.mem_union_right _ hmem)
private theorem Pattern.henkinFresh_not_mem_stage_FV
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    ∀ q ∈ ({q | q ∈ l} : Set (Pattern S Nat)), henkinFresh l p ∉ FV q := by
  intro q hq hfree
  apply (Pattern.imp (listSupport l) p).fresh_not_mem_allVars
  apply Finset.mem_union_left
  exact allVars_subset_listSupport hq (q.FV_subset_allVars hfree)
private theorem listTheory_subset_addWitness (l : List (Pattern S Nat))
    (phi : Pattern S Nat) :
    ({q | q ∈ l} : Set (Pattern S Nat)) ⊆ {q | q ∈ addWitness l phi} := by
  intro q hq
  cases phi <;> simp_all [addWitness]
private theorem locConsistent_addWitness (l : List (Pattern S Nat))
    (phi : Pattern S Nat) (hl : LocConsistent ({q | q ∈ l} : Set (Pattern S Nat))) :
    LocConsistent ({q | q ∈ addWitness l phi} : Set (Pattern S Nat)) := by
  cases phi with
  | var x => simpa [addWitness] using hl
  | bot => simpa [addWitness] using hl
  | app sigma args => simpa [addWitness] using hl
  | imp p q => simpa [addWitness] using hl
  | ex x p =>
      let y := Pattern.henkinFresh l p
      have hcons := locConsistent_insert_captureAvoidingWitness
        (Gamma := ({q | q ∈ l} : Set (Pattern S Nat))) (x := x) (y := y) (p := p)
        hl (Pattern.henkinFresh_not_mem_stage_FV l p)
        (Pattern.henkinFresh_not_mem_body l p)
      rw [show
        ({q | q ∈ addWitness l (.ex x p)} : Set (Pattern S Nat)) =
          insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
            ({q | q ∈ l} : Set (Pattern S Nat)) by
          ext q
          simp [addWitness, y]]
      exact hcons
private theorem witnessStages_locConsistent (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∀ n, LocConsistent ({q | q ∈ witnessStages enum base n} : Set (Pattern S Nat)) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      simpa [henkinStages] using
        locConsistent_addWitness (witnessStages enum base n) (enum n) ih
private theorem henkinTheory_locConsistent (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    LocConsistent (henkinTheory enum base) := by
  exact henkinLimit_locConsistent (fun l => {q | q ∈ l}) addWitness enum base
    listTheory_subset_addWitness
    (witnessStages_locConsistent enum base hbase)
private theorem base_subset_henkinTheory (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) :
    ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ henkinTheory enum base := by
  intro q hq
  exact ⟨0, hq⟩
private theorem henkinTheory_has_freshWitness
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat)) (x : Nat) (p : Pattern S Nat) :
    ∃ y, y ∉ p.allVars ∧ .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈
      henkinTheory enum base := by
  obtain ⟨n, hn⟩ := henum (.ex x p)
  let y := Pattern.henkinFresh (witnessStages enum base n) p
  refine ⟨y, Pattern.henkinFresh_not_mem_body _ _, n + 1, ?_⟩
  simp [henkinStages, hn, addWitness, y]
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
theorem _root_.solution
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ FreshWitnessed Delta := by
  obtain ⟨Delta, hHDelta, hM⟩ :=
    locConsistent_extend_isMCS (henkinTheory_locConsistent enum base hbase)
  refine ⟨Delta, (base_subset_henkinTheory enum base).trans hHDelta, hM, ?_⟩
  intro x p _hex
  obtain ⟨y, hyfresh, hy⟩ := henkinTheory_has_freshWitness enum henum base x p
  exact ⟨y, hyfresh, hHDelta hy⟩
end MatchingLogic
