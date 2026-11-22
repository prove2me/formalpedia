-- Prove2me | solution 1 for MatchingLogic.NaryStageSystem.canonicalExistence_of_stageSystem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:56.936095+00:00
-- url     : https://prove2.me/submissions/722c6374-8b0a-4181-8667-a95a3366e8f7

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Theorems.Thm_MatchingLogic_NaryStageSystem_limit_contains_base
public import Theorems.Thm_MatchingLogic_NaryStageSystem_root_mem_canonicalInterp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
open MatchingLogic.NaryStageSystem
variable {sigma : S.Sym} {Gamma : CanonicalCarrier S}
  {phi : Fin (S.arity sigma) → Pattern S Nat} {enum : Nat → Pattern S Nat}
  (T : NaryStageSystem sigma Gamma phi enum)
namespace MatchingLogic.NaryStageSystem
theorem _root_.solution
    (T : NaryStageSystem sigma Gamma phi enum) (henum : Function.Surjective enum) :
    ∃ components : Fin (S.arity sigma) → CanonicalCarrier S,
      (∀ i, phi i ∈ (components i).val) ∧
        Gamma ∈ canonicalInterp sigma components := by
  let components : Fin (S.arity sigma) → CanonicalCarrier S := fun i =>
    ⟨NaryStageSystem.limit T i,
      ⟨NaryStageSystem.limit_isMCS T henum i, NaryStageSystem.limit_freshWitnessed T henum i⟩⟩
  refine ⟨components, ?_, ?_⟩
  · intro i
    exact NaryStageSystem.limit_contains_base T i
  · exact NaryStageSystem.root_mem_canonicalInterp T henum
end MatchingLogic.NaryStageSystem
