-- Prove2me | solution 1 for MatchingLogic.Pattern.signatureNatCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:42.847389+00:00
-- url     : https://prove2.me/submissions/30b65021-94b1-41c4-bf8e-314f3e3a1185

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace Signature
end Signature
namespace Pattern
end Pattern
namespace AppCtx
end AppCtx
namespace Pattern
private theorem signatureNatTag_eq_of_code_eq {T : Signature} [Encodable T.Sym]
    {p q : Pattern T Nat} (h : p.signatureNatCode = q.signatureNatCode) :
    signatureNatTag p = signatureNatTag q := by
  have h' := congrArg (fun n => (Nat.unpair n).1) h
  cases p <;> cases q <;>
    simp [signatureNatTag, signatureNatCode] at h' ⊢
end Pattern
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution {T : Signature} [Encodable T.Sym] :
    Function.Injective (@signatureNatCode T _) := by
  intro p
  induction p with
  | var x =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case var y =>
        exact congrArg Pattern.var (Nat.pair_eq_pair.mp h).2
      all_goals simp [signatureNatTag] at htag
  | bot =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case bot => rfl
      all_goals simp [signatureNatTag] at htag
  | imp p q ihp ihq =>
      intro r h
      have htag := signatureNatTag_eq_of_code_eq h
      cases r
      case imp p' q' =>
        have hpq := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        cases ihp hpq.1
        cases ihq hpq.2
        rfl
      all_goals simp [signatureNatTag] at htag
  | ex x p ih =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case ex y q =>
        have hxp := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        cases hxp.1
        cases ih hxp.2
        rfl
      all_goals simp [signatureNatTag] at htag
  | app sigma args ih =>
      intro q h
      have htag := signatureNatTag_eq_of_code_eq h
      cases q
      case app tau bs =>
        have hsargs := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
        have hst : sigma = tau := Encodable.encode_injective hsargs.1
        subst tau
        have hargs : List.ofFn (fun i => (args i).signatureNatCode) =
            List.ofFn (fun i => (bs i).signatureNatCode) :=
          Encodable.encode_injective hsargs.2
        congr
        funext i
        apply ih i
        exact congrFun (List.ofFn_injective hargs) i
      all_goals simp [signatureNatTag] at htag
end MatchingLogic.Pattern
