-- Prove2me | solution 1 for MatchingLogic.canonicalExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:05.267826+00:00
-- url     : https://prove2.me/submissions/969a6d50-6944-4c3a-83a4-90349bc2c551

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Theorems.Thm_MatchingLogic_NaryStageSystem_canonicalExistence_of_stageSystem


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution [Countable (Pattern S Nat)] : CanonicalExistenceProperty S := by
  intro Gamma sigma args happ
  let _ : Nonempty (Pattern S Nat) := ⟨.bot⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Pattern S Nat)
  exact NaryStageSystem.canonicalExistence_of_stageSystem
    (constructedStages Gamma args happ enum) henum
end MatchingLogic
