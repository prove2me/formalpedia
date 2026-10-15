-- Prove2me | solution 1 for OAI.QAC.projection_transition_square
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:02:54.893443+00:00
-- url     : https://prove2.me/submissions/5ae86461-cd72-4a2c-a390-76be9e64dd33

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean:L28-L47
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.projection_transition_square. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

-- ---- from OAI.InformationTheory.QuantumCircuit.Spectral ----
-- Lean 4.34 name of List.sum_le_card_nsmul (same statement) in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma norm_mul_le_right {A : Type*} [NormedRing A] (x y : A) (hx : ‖x‖ ≤ 1) :
    ‖x*y‖ ≤ ‖y‖ := (norm_mul_le _ _).trans (by nlinarith only [hx, norm_nonneg y])

lemma norm_mul_le_left {A : Type*} [NormedRing A] (x y : A) (hy : ‖y‖ ≤ 1) :
    ‖x*y‖ ≤ ‖x‖ := (norm_mul_le _ _).trans (by nlinarith only [hy, norm_nonneg x])

end QAC

end

end OAI

-- ---- from OAI.InformationTheory.QuantumCircuit.Transition ----
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma projection_transition_square (H P Q X : A)
    (hH : IsStarProjection H) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖H * Q * P‖^2 ≤ ‖H * X * P‖ + ‖(Q-X) * P * Q‖ := by
  have hid : (H*Q*P) * star (H*Q*P) = H*Q*P*Q*H := by
    simp only [star_mul, hH.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq]
    calc
      _ = H * Q * (P*P) * Q * H := by simp only [mul_assoc]
      _ = _ := by rw [hP.isIdempotentElem.eq]
  have heq : H*Q*P*Q*H = (H*X*P)*Q*H + H*((Q-X)*P*Q)*H := by noncomm_ring
  calc
    ‖H*Q*P‖^2 = ‖(H*Q*P) * star (H*Q*P)‖ := by rw [CStarRing.norm_self_mul_star]; ring
    _ = ‖(H*X*P)*Q*H + H*((Q-X)*P*Q)*H‖ := by rw [hid,heq]
    _ ≤ ‖(H*X*P)*Q*H‖ + ‖H*((Q-X)*P*Q)*H‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hQ))
      · exact (norm_mul_le_left _ _ (IsStarProjection.norm_le _ hH)).trans
          (norm_mul_le_right _ _ (IsStarProjection.norm_le _ hH))

end NormAlgebra

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

end Conjugation

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix
variable {A : Type*} [CStarAlgebra A]

theorem solution (H P Q X : A)
    (hH : IsStarProjection H) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖H * Q * P‖^2 ≤ ‖H * X * P‖ + ‖(Q-X) * P * Q‖ := by
  first
    | exact OAI.QAC.projection_transition_square H P Q X hH hP hQ
    | exact OAI.QAC.projection_transition_square
    | (apply OAI.QAC.projection_transition_square <;> assumption)
    | (intros; apply OAI.QAC.projection_transition_square <;> assumption)
