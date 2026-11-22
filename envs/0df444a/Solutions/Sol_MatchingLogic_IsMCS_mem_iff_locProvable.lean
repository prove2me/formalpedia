-- Prove2me | solution 1 for MatchingLogic.IsMCS.mem_iff_locProvable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:44.329618+00:00
-- url     : https://prove2.me/submissions/75d1b966-c78b-4d46-ad7c-79ae7d2afb29

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_LocProvable_of_mem
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_deduction_insert
section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] instDecidableEqPatternLocalTheory
namespace LocProvable
end LocProvable
namespace IsMCS
private theorem not_mem_loc_neg {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) (hphi : phi ∉ Gamma) : LocProvable Gamma (Pattern.nt phi) := by
  by_contra hneg
  have hstrict : Gamma ⊂ insert phi Gamma := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_insert _ _, ?_⟩
    intro hEq
    exact hphi (hEq ▸ Set.mem_insert phi Gamma)
  have hbad : ¬ LocConsistent (insert phi Gamma) := hM.2 hstrict
  apply hbad
  intro hbot
  exact hneg (hbot.deduction_insert)
end IsMCS
end
end MatchingLogic
end
end

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
theorem _root_.solution {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hM : IsMCS Gamma) : phi ∈ Gamma ↔ LocProvable Gamma phi := by
  constructor
  · exact LocProvable.of_mem
  · intro hphi
    by_contra hnot
    have hneg := not_mem_loc_neg hM hnot
    apply hM.1
    exact hphi.mp hneg
end MatchingLogic.IsMCS
