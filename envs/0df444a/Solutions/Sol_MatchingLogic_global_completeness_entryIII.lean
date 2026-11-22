-- Prove2me | solution 1 for MatchingLogic.global_completeness_entryIII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:25.880068+00:00
-- url     : https://prove2.me/submissions/82a743f6-1f29-46ab-876f-c9419ecbc131

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness
public import Theorems.Thm_MatchingLogic_global_completeness_of_localCompleteness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution {Var : Type}
    [DecidableEq Var] [Denumerable Var]
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGamma : ∀ gamma ∈ Gamma, Closed gamma) (hphi : Closed phi) :
    GlobalCons Gamma phi ↔ Provable Gamma phi :=
  global_completeness_of_localCompleteness strongLocalCompleteness hGamma hphi
end MatchingLogic
