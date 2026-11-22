-- Prove2me | solution 1 for MatchingLogic.locConsistent_extend_freshWitnessed_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:45.500734+00:00
-- url     : https://prove2.me/submissions/706ead0b-f717-429a-a6a5-54972b84d6b4

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessSupply
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
public import Theorems.Thm_MatchingLogic_Pattern_allVars_subset_listSupport
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_henkinLimit_locConsistent
public import Theorems.Thm_MatchingLogic_locConsistent_extend_isMCS
public import Theorems.Thm_MatchingLogic_locConsistent_insert_captureAvoidingWitness
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
private theorem Pattern.supplyFresh_mem_reserve
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∈ {y : Nat | ∀ q ∈ Gamma, y ∉ FV q} :=
  (Classical.choose_spec
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))).1
private theorem Pattern.supplyFresh_not_mem_blocked
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∉
      (listSupport l).allVars ∪ p.allVars :=
  (Classical.choose_spec
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))).2
private theorem Pattern.supplyFresh_not_mem_body
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    supplyFresh Gamma hSupply l p ∉ p.allVars := by
  intro hp
  exact supplyFresh_not_mem_blocked Gamma hSupply l p
    (Finset.mem_union_right _ hp)
private theorem Pattern.supplyFresh_not_mem_stage_FV
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) :
    ∀ q ∈ supplyStageTheory Gamma l, supplyFresh Gamma hSupply l p ∉ FV q := by
  intro q hq
  rcases hq with hqGamma | hqList
  · exact supplyFresh_mem_reserve Gamma hSupply l p q hqGamma
  · intro hfree
    apply supplyFresh_not_mem_blocked Gamma hSupply l p
    apply Finset.mem_union_left
    exact allVars_subset_listSupport hqList (q.FV_subset_allVars hfree)
private theorem supplyStageTheory_subset_addWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (phi : Pattern S Nat) :
    supplyStageTheory Gamma l ⊆
      supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l phi) := by
  intro q hq
  rcases hq with hq | hq
  · exact Set.mem_union_left _ hq
  · exact Set.mem_union_right _ (by
      cases phi <;> simp_all [supplyAddWitness])
private theorem locConsistent_supplyAddWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (phi : Pattern S Nat)
    (hl : LocConsistent (supplyStageTheory Gamma l)) :
    LocConsistent
      (supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l phi)) := by
  cases phi with
  | var x => simpa [supplyAddWitness] using hl
  | bot => simpa [supplyAddWitness] using hl
  | app sigma args => simpa [supplyAddWitness] using hl
  | imp p q => simpa [supplyAddWitness] using hl
  | ex x p =>
      let y := Pattern.supplyFresh Gamma hSupply l p
      have hcons := locConsistent_insert_captureAvoidingWitness
        (Gamma := supplyStageTheory Gamma l) (x := x) (y := y) (p := p) hl
        (Pattern.supplyFresh_not_mem_stage_FV Gamma hSupply l p)
        (Pattern.supplyFresh_not_mem_body Gamma hSupply l p)
      rw [show
        supplyStageTheory Gamma (supplyAddWitness Gamma hSupply l (.ex x p)) =
          insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
            (supplyStageTheory Gamma l) by
          ext q
          simp [supplyStageTheory, supplyAddWitness, y]
          tauto]
      exact hcons
private theorem supplyWitnessStages_locConsistent
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (hGamma : LocConsistent Gamma) :
    ∀ n, LocConsistent
      (supplyStageTheory Gamma (supplyWitnessStages Gamma hSupply enum n)) := by
  intro n
  induction n with
  | zero => simpa [henkinStages, supplyStageTheory] using hGamma
  | succ n ih =>
      simpa [henkinStages] using
        locConsistent_supplyAddWitness Gamma hSupply
          (supplyWitnessStages Gamma hSupply enum n) (enum n) ih
private theorem suppliedHenkinTheory_locConsistent
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (hGamma : LocConsistent Gamma) :
    LocConsistent (suppliedHenkinTheory Gamma hSupply enum) := by
  exact henkinLimit_locConsistent (supplyStageTheory Gamma)
    (supplyAddWitness Gamma hSupply) enum []
    (supplyStageTheory_subset_addWitness Gamma hSupply)
    (supplyWitnessStages_locConsistent Gamma hSupply enum hGamma)
private theorem Gamma_subset_suppliedHenkinTheory
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) :
    Gamma ⊆ suppliedHenkinTheory Gamma hSupply enum := by
  intro q hq
  exact ⟨0, Set.mem_union_left _ hq⟩
private theorem suppliedHenkinTheory_has_freshWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (x : Nat) (p : Pattern S Nat) :
    ∃ y, y ∉ p.allVars ∧
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈
        suppliedHenkinTheory Gamma hSupply enum := by
  obtain ⟨n, hn⟩ := henum (.ex x p)
  let l := supplyWitnessStages Gamma hSupply enum n
  let y := Pattern.supplyFresh Gamma hSupply l p
  refine ⟨y, Pattern.supplyFresh_not_mem_body Gamma hSupply l p, n + 1, ?_⟩
  apply Set.mem_union_right
  simp [henkinStages, hn, supplyAddWitness, l, y]
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
attribute [local instance] MatchingLogic.witnessSupplyDecidableEqPattern
namespace MatchingLogic
theorem _root_.solution
    [Countable (Pattern S Nat)] {Gamma : Set (Pattern S Nat)}
    (hGamma : LocConsistent Gamma)
    (hSupply : InfiniteFreshVariableSupply Gamma) :
    ∃ Delta : Set (Pattern S Nat),
      Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta := by
  let _ : Nonempty (Pattern S Nat) := ⟨.bot⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Pattern S Nat)
  obtain ⟨Delta, hHenkinDelta, hM⟩ :=
    locConsistent_extend_isMCS
      (suppliedHenkinTheory_locConsistent Gamma hSupply enum hGamma)
  refine ⟨Delta,
    (Gamma_subset_suppliedHenkinTheory Gamma hSupply enum).trans hHenkinDelta,
    hM, ?_⟩
  intro x p _hex
  obtain ⟨y, hyFresh, hyWitness⟩ :=
    suppliedHenkinTheory_has_freshWitness Gamma hSupply enum henum x p
  exact ⟨y, hyFresh, hHenkinDelta hyWitness⟩
end MatchingLogic
