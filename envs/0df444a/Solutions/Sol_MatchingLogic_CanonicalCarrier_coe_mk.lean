-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.coe_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:42.832305+00:00
-- url     : https://prove2.me/submissions/8fda89c8-1426-457f-af9b-12a09d993eef

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore
open MatchingLogic.CanonicalCarrier
namespace MatchingLogic.CanonicalCarrier
theorem _root_.solution (Gamma : Set (Pattern S Nat))
    (h : IsMCS Gamma ∧ FreshWitnessed Gamma) :
    ((⟨Gamma, h⟩ : CanonicalCarrier S) : Set (Pattern S Nat)) = Gamma :=
  rfl
end MatchingLogic.CanonicalCarrier
