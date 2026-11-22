-- Prove2me | solution 1 for MatchingLogic.localCons_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:54.361997+00:00
-- url     : https://prove2.me/submissions/b05f2435-eb2d-4615-bde0-17f1ebcce7ce

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
public import Theorems.Thm_MatchingLogic_EntryIII_localCons_compact

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi :=
  EntryIII.localCons_compact hlocal
end MatchingLogic
