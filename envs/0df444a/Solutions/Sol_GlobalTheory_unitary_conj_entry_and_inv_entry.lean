-- Prove2me | solution 1 for GlobalTheory.unitary_conj_entry_and_inv_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:38.863435+00:00
-- url     : https://prove2.me/submissions/6b02b18e-91b6-4fd2-b48d-be0cc3025368

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BesselJUnitaryEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryConjEntryAndInvEntryLinear
import Theorems.Thm_GlobalTheory_sandwich_entry_sum
import Theorems.Thm_GlobalTheory_unitary_inv_eq_gram_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  intro k r i j
  refine ⟨⟨fun a b => Hpk k r j a * Hpk k r b i, fun g hg => ?_⟩,
    fun g => (Hpk k r * gᴴ * Hpk k r) i j, ?_, fun g hg => by rw [unitary_inv_eq_gram_conj hg]⟩
  · have h : gᴴ = Hpk k r * g⁻¹ * Hpk k r := by
      rw [unitary_inv_eq_gram_conj hg]
      simp only [← mul_assoc]
      rw [BesselUnitary.gram_sq, one_mul, mul_assoc, BesselUnitary.gram_sq, mul_one]
    rw [← sandwich_entry_sum, ← h, Matrix.conjTranspose_apply]
  · refine ⟨∑ a, ∑ b, MvPolynomial.C (Hpk k r i a * Hpk k r b j) * MvPolynomial.X (Sum.inr (b, a)), ?_, fun g => ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun a _ =>
        MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · show (Hpk k r * gᴴ * Hpk k r) i j = _
      rw [sandwich_entry_sum]
      simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr,
        Matrix.conjTranspose_apply]
end GlobalTheory
