-- Prove2me | solution 1 for MatchingLogic.IsMCS.freshWitness_elim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:02.069649+00:00
-- url     : https://prove2.me/submissions/efd13060-36f7-4fd9-b91f-61fd83458020

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Theorems.Thm_MatchingLogic_IsMCS_mp_mem


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) (hW : FreshWitnessed Gamma) {y : Nat} {q : Pattern S Nat}
    (hmem : Pattern.ex y q ∈ Gamma) :
    ∃ z, z ∉ q.allVars ∧ Pattern.captureAvoidingSubst y z q ∈ Gamma := by
  obtain ⟨z, hzfresh, himp⟩ := hW hmem
  exact ⟨z, hzfresh, hM.mp_mem hmem himp⟩
end IsMCS
end MatchingLogic
