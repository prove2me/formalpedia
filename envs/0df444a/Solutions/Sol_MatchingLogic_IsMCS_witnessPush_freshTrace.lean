-- Prove2me | solution 1 for MatchingLogic.IsMCS.witnessPush_freshTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:05.941799+00:00
-- url     : https://prove2.me/submissions/1b901dd7-bdfd-4a80-a415-22786d439aa0

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Theorems.Thm_MatchingLogic_IsMCS_exList_freshWitness_elim
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
public import Theorems.Thm_MatchingLogic_Provable_witnessPush
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
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



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (p : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyfreshP : forall i, y i ∉ p.allVars)
    (hyfreshPhi : forall i j, y i ∉ (Phi j).allVars)
    (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ z : List Nat,
      Pattern.FreshExListTrace (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∧
      Pattern.substList (List.ofFn y) z
        (.app sigma (fun i => Pattern.and (Phi i)
          (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma := by
  let body : Pattern S Nat := .app sigma (fun i => Pattern.and (Phi i)
    (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))
  have hpush : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi) (Pattern.exList (List.ofFn y) body)) := by
    simpa [body] using Provable.witnessPush Phi p x y hyinj
      (fun i h => hyfreshP i (p.FV_subset_allVars h))
      (fun i j h => hyfreshPhi i j ((Phi j).FV_subset_allVars h))
  have hnested : Pattern.exList (List.ofFn y) body ∈ Gamma :=
    hM.mem_of_provable_imp happ hpush
  have hnodup : (List.ofFn y).Nodup := by
    rw [List.nodup_ofFn]
    exact hyinj
  simpa [body] using hM.exList_freshWitness_elim hW (List.ofFn y) hnodup body hnested
end IsMCS
end MatchingLogic
