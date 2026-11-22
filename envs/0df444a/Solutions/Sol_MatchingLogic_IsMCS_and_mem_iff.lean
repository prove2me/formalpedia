-- Prove2me | solution 1 for MatchingLogic.IsMCS.and_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:05.979095+00:00
-- url     : https://prove2.me/submissions/67860502-81e4-4641-ad3c-49bf9c4a0929

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_Provable_and_elim_left
public import Theorems.Thm_MatchingLogic_Provable_and_elim_right
public import Theorems.Thm_MatchingLogic_LocProvable_of_provable
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_and_intro
public import Theorems.Thm_MatchingLogic_IsMCS_mem_iff_locProvable
public import Theorems.Thm_MatchingLogic_Provable_and_intro


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.IsMCS
namespace MatchingLogic.IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hM : IsMCS Gamma) : Pattern.and phi psi ∈ Gamma ↔ phi ∈ Gamma ∧ psi ∈ Gamma := by
  constructor
  · intro hand
    constructor
    · exact hM.mem_iff_locProvable.mpr
        ((hM.mem_iff_locProvable.mp hand).mp
          (LocProvable.of_provable (Provable.and_elim_left _ phi psi)))
    · exact hM.mem_iff_locProvable.mpr
        ((hM.mem_iff_locProvable.mp hand).mp
          (LocProvable.of_provable (Provable.and_elim_right _ phi psi)))
  · rintro ⟨hphi, hpsi⟩
    exact hM.mem_iff_locProvable.mpr
      ((hM.mem_iff_locProvable.mp hphi).and_intro (hM.mem_iff_locProvable.mp hpsi))
end MatchingLogic.IsMCS
