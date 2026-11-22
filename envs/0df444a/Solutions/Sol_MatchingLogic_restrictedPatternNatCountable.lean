-- Prove2me | solution 1 for MatchingLogic.restrictedPatternNatCountable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:46.945812+00:00
-- url     : https://prove2.me/submissions/0055c80e-6bfb-4019-93c2-68a2982eaab3

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Theorems.Thm_MatchingLogic_Pattern_signatureNatCode_injective

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution
    (F : Finset S.Sym) : Countable (Pattern (S.restrict F) Nat) := by
  classical
  let : Fintype (S.restrict F).Sym := by
    unfold Signature.restrict
    infer_instance
  let : Encodable (S.restrict F).Sym :=
    Encodable.ofEquiv (Fin (Fintype.card (S.restrict F).Sym))
      (Fintype.equivFin (S.restrict F).Sym)
  exact ⟨Pattern.signatureNatCode, Pattern.signatureNatCode_injective⟩
end MatchingLogic
