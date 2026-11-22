-- Prove2me | solution 1 for MatchingLogic.Provable.alphaEx_backward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:25.656065+00:00
-- url     : https://prove2.me/submissions/aaa98d04-59e0-4d88-8720-e6bcf2d4b902

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Theorems.Thm_MatchingLogic_Pattern_captureFree_of_not_mem_allVars
public import Theorems.Thm_MatchingLogic_Pattern_FV_subset_allVars


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex y (substVar x y p)) (.ex x p)) := by
  exact .exGen (.exQuant (Pattern.captureFree_of_not_mem_allVars hy)) (by
    intro hymem
    exact hy (p.FV_subset_allVars hymem.1))
end Provable
end MatchingLogic
