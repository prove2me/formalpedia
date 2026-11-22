-- Prove2me | solution 1 for MatchingLogic.witnessCollapseTheory_isMCS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:20.214428+00:00
-- url     : https://prove2.me/submissions/52241e6b-f528-40b7-be9e-d2f847df35d0

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Theorems.Thm_MatchingLogic_pointedTheory_isMCS

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution : IsMCS witnessCollapseTheory := by
  exact pointedTheory_isMCS witnessCollapseModel witnessCollapseRho true
end MatchingLogic
