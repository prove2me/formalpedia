-- Prove2me | solution 1 for GlobalTheory.CuspGL.PsiPrimitive.psi_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:09.383615+00:00
-- url     : https://prove2.me/submissions/9f30e7d2-6a04-4398-ab8e-fc0332bd078e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PsiPrimitive
namespace GlobalTheory.CuspGL.PsiPrimitive
theorem _root_.solution {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Subsingleton V] (g : Module.End F V) :
    psi s V g = 0 := by
  rw [psi_eq s V g]
  have hpoly : LinearMap.charpoly g = 1 := by
    have hdeg : (LinearMap.charpoly g).natDegree = 0 := by
      rw [LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g) hdeg
  have hs1 : s 1 = 0 := by
    have h11 := hs 1 1 monic_one monic_one
    rw [one_mul] at h11
    linear_combination -h11
  have hempty : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} := by
    refine ⟨fun W => W.2.1 ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    rw [Subsingleton.elim x 0]
    exact W.1.zero_mem
  rw [hpoly, hs1, finsum_of_isEmpty, sub_zero]
end GlobalTheory.CuspGL.PsiPrimitive
