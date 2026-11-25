-- Prove2me | solution 1 for GlobalTheory.DeligneSerre.unitBall_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:16.53929+00:00
-- url     : https://prove2.me/submissions/0cc14cfb-7349-44f3-b06a-c432edf3cae5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.DeligneSerre
namespace GlobalTheory.DeligneSerre
theorem _root_.solution (R : Type) [CommRing R] (l : ℕ) [Fact l.Prime] (χ : R →+* PadicAlgCl l)
    (h : ∀ p, ‖χ p‖ ≤ 1) : ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 := by
  refine ⟨{ carrier := {p | ‖χ p‖ < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_,
    fun p => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  · simp
  · intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖χ c‖ * ‖χ x‖ ≤ 1 * ‖χ x‖ := by gcongr; exact h c
      _ < 1 := by simpa using hx
  · refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ ‖χ 1‖ < 1
      simp
    · intro a b hab
      show ‖χ a‖ < 1 ∨ ‖χ b‖ < 1
      have hab' : ‖χ a‖ * ‖χ b‖ < 1 := by
        have : ‖χ (a * b)‖ < 1 := hab
        simpa [map_mul, norm_mul] using this
      by_contra hno
      push_neg at hno
      have : 1 * 1 ≤ ‖χ a‖ * ‖χ b‖ := mul_le_mul hno.1 hno.2 zero_le_one (norm_nonneg _)
      linarith
end GlobalTheory.DeligneSerre
