-- Prove2me | solution 1 for GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:11.460698+00:00
-- url     : https://prove2.me/submissions/b5e3fe31-b736-4adc-9b1d-777cf334a24a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
import Theorems.Thm_GlobalTheory_CuspGL_exponent_regular_of_natDegree_minpoly_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  first | exact @GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | exact GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | (intros; apply GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow <;> assumption)
end _root_.GlobalTheory.T
