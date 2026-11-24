-- Prove2me | solution 1 for GlobalTheory.character_one_mul_sum_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:43.353904+00:00
-- url     : https://prove2.me/submissions/19428481-f240-4af6-af24-1d32c72df5b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
import Theorems.Thm_GlobalTheory_exists_sum_conj_eq_smul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x y : G) :
    ρ.character 1 * ∑ h : G, ρ.character (h * x * h⁻¹ * y)
      = (Fintype.card G : ℂ) * (ρ.character x * ρ.character y) := by
  obtain ⟨c, hc⟩ := exists_sum_conj_eq_smul_one ρ x
  have key : ∀ z : G, ∑ h : G, ρ.character (h * x * h⁻¹ * z) = c * ρ.character z := by
    intro z
    have := congrArg (fun A => LinearMap.trace ℂ V (A * ρ z)) hc
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← map_mul] at this
    exact this
  have h1 := key 1
  simp only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [key y, ← mul_assoc, mul_comm _ c, ← h1, mul_assoc]
end GlobalTheory
