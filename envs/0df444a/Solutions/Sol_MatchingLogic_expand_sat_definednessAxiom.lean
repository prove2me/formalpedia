-- Prove2me | solution 1 for MatchingLogic.expand_sat_definednessAxiom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:15.374905+00:00
-- url     : https://prove2.me/submissions/9aa28995-9900-4feb-88b2-2e8e7250b0ab

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) (x : Var) :
    (expand M).Sat (definednessAxiom (S := S) x) := by
  intro ρ
  unfold Model.Total
  change (expand M).app none (fun _ => ({ρ x} : Set M.carrier)) = Set.univ
  apply Set.eq_univ_iff_forall.mpr
  intro u
  exact ⟨fun _ => ρ x, fun _ => Set.mem_singleton (ρ x), Set.mem_univ u⟩
end MatchingLogic
