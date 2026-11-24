-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.stab_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:33.067123+00:00
-- url     : https://prove2.me/submissions/568b1cb0-7dc5-4c9e-9be7-7780ff28aade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_eq
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_finite_end
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_indicator_split
import Theorems.Thm_GlobalTheory_T_charpoly_block_and_invariant_under_stabilizerNilradical
import Theorems.Thm_GlobalTheory_T_finsum_subspaceStabilizer_mul_block_functions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult
open Classical
namespace GlobalTheory.CuspGL.MassMult
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (φ : Module.End F W → ℂ) (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        (mass φ x.1 * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) x.2) := by
  have := finite_end F V
  have := Fintype.ofFinite {g : Module.End F V // ∀ x ∈ W, g x ∈ W}
  have key : ∀ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
      (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (if LinearMap.charpoly (g.1.restrict g.2) = x.1 then φ (g.1.restrict g.2) else 0) *
        (if LinearMap.charpoly (W.mapQ W g.1 (fun x hx => g.2 x hx)) = x.2 then (1 : ℂ) else 0) := by
    intro g
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V W g.1 g.2).1
    exact indicator_split P T hT (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) hc _
  rw [finsum_congr key, finsum_eq_sum_of_fintype, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mass_eq, mass_eq, ← finsum_eq_sum_of_fintype]
  exact GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions F V W (fun a => if LinearMap.charpoly a = x.1 then φ a else 0)
    (fun b => if LinearMap.charpoly b = x.2 then (1 : ℂ) else 0)
end GlobalTheory.CuspGL.MassMult
