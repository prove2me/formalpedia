-- Prove2me | solution 1 for MatchingLogic.IsMCS.witnessPush_elim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:53.778612+00:00
-- url     : https://prove2.me/submissions/8e881635-edaf-4cf8-9ee9-d94110865f9b

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
public import Theorems.Thm_MatchingLogic_IsMCS_exList_witness_elim
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars
public import Theorems.Thm_MatchingLogic_Provable_witnessPush


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
    ∃ z : Fin (S.arity sigma) -> Nat,
      (forall i, z i ∉ p.allVars) ∧
      (forall i j, z i ∉ (Phi j).allVars) ∧
      Pattern.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (z i) p))) ∈ Gamma := by
  have hpush : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi)
        (Pattern.exList (List.ofFn y)
          (.app sigma (fun i => Pattern.and (Phi i)
            (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))))) := by
    exact Provable.witnessPush Phi p x y hyinj
      (fun i h => hyfreshP i (p.FV_subset_allVars h))
      (fun i j h => hyfreshPhi i j ((Phi j).FV_subset_allVars h))
  have hnested : Pattern.exList (List.ofFn y)
      (.app sigma (fun i => Pattern.and (Phi i)
        (.imp (.ex x p) (Pattern.captureAvoidingSubst x (y i) p)))) ∈ Gamma :=
    hM.mem_of_provable_imp happ hpush
  exact hM.exList_witness_elim hW Phi p x y hyinj hyfreshP hyfreshPhi hnested
end IsMCS
end MatchingLogic
