-- Prove2me | solution 1 for MatchingLogic.IsMCS.mp_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:22.824346+00:00
-- url     : https://prove2.me/submissions/ea7330d2-ed39-4d5a-884e-63c93e8b773d

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_IsMCS_mem_iff_locProvable

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
    (hM : IsMCS Gamma) (hphi : phi ∈ Gamma) (himp : Pattern.imp phi psi ∈ Gamma) :
    psi ∈ Gamma :=
  hM.mem_iff_locProvable.mpr ((hM.mem_iff_locProvable.mp hphi).mp
    (hM.mem_iff_locProvable.mp himp))
end MatchingLogic.IsMCS
