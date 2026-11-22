-- Prove2me | solution 1 for MatchingLogic.CanonicalCarrier.exists_var_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:17.693293+00:00
-- url     : https://prove2.me/submissions/062113df-5f52-49e5-8c45-56fcaadd229f

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_isMCS
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_witnessed
public import Theorems.Thm_MatchingLogic_IsMCS_exists_var_mem_of_witnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore
namespace MatchingLogic
namespace CanonicalCarrier
theorem _root_.solution (Gamma : CanonicalCarrier S) :
    ∃ y : Nat, Pattern.var y ∈ Gamma.val :=
  (CanonicalCarrier.isMCS Gamma).exists_var_mem_of_witnessed
    (CanonicalCarrier.witnessed Gamma)
end CanonicalCarrier
end MatchingLogic
