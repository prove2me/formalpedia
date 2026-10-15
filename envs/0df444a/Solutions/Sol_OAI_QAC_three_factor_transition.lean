-- Prove2me | solution 1 for OAI.QAC.three_factor_transition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:07:26.78886+00:00
-- url     : https://prove2.me/submissions/bf1d909e-76a7-4be9-ac64-77ce1791f326

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean:L153-L172
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.three_factor_transition. The node keeps its source
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

end NormAlgebra

lemma norm_mul_le_one {A : Type*} [NormedRing A] {x y : A}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x*y‖ ≤ 1 :=
  (norm_mul_le_left _ _ hy).trans hx

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

lemma three_factor_transition (H P H₁ H₂ B₁ B₂ B₃ : A) {δ : ℝ}
    (hH : ‖H‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hE₁ : ‖1-H₁‖ ≤ 1)
    (hB₁ : ‖B₁‖ ≤ 1) (hB₂ : ‖B₂‖ ≤ 1) (hB₃ : ‖B₃‖ ≤ 1)
    (h₁ : ‖H₁*B₃*P‖ ≤ δ) (h₂ : ‖H₂*B₂*(1-H₁)‖ ≤ δ)
    (h₃ : ‖H*B₁*(1-H₂)‖ ≤ δ) : ‖H*B₁*B₂*B₃*P‖ ≤ 3*δ := by
  have heq : H*B₁*B₂*B₃*P = (H*B₁*B₂)*(H₁*B₃*P) +
      (H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P) +
      (H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P) := by noncomm_ring
  have ht₁ : ‖(H*B₁*B₂)*(H₁*B₃*P)‖ ≤ δ :=
    (norm_mul_le_right _ _ (norm_mul_le_one (norm_mul_le_one hH hB₁) hB₂)).trans h₁
  have ht₂ : ‖(H*B₁)*(H₂*B₂*(1-H₁))*(B₃*P)‖ ≤ δ :=
    ((norm_mul_le_left _ _ (norm_mul_le_one hB₃ hP)).trans
      (norm_mul_le_right _ _ (norm_mul_le_one hH hB₁))).trans h₂
  have ht₃ : ‖(H*B₁*(1-H₂))*(B₂*(1-H₁)*B₃*P)‖ ≤ δ :=
    (norm_mul_le_left _ _ (norm_mul_le_one (norm_mul_le_one
      (norm_mul_le_one hB₂ hE₁) hB₃) hP)).trans h₃
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (by linarith only [ht₁,ht₂,ht₃]))
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

theorem solution (H P H₁ H₂ B₁ B₂ B₃ : A) {δ : ℝ}
    (hH : ‖H‖ ≤ 1) (hP : ‖P‖ ≤ 1)
    (hE₁ : ‖1-H₁‖ ≤ 1)
    (hB₁ : ‖B₁‖ ≤ 1) (hB₂ : ‖B₂‖ ≤ 1) (hB₃ : ‖B₃‖ ≤ 1)
    (h₁ : ‖H₁*B₃*P‖ ≤ δ) (h₂ : ‖H₂*B₂*(1-H₁)‖ ≤ δ)
    (h₃ : ‖H*B₁*(1-H₂)‖ ≤ δ) : ‖H*B₁*B₂*B₃*P‖ ≤ 3*δ := by
  first
    | exact OAI.QAC.three_factor_transition H P H₁ H₂ B₁ B₂ B₃ hH hP hE₁ hB₁ hB₂ hB₃ h₁ h₂ h₃
    | exact OAI.QAC.three_factor_transition
    | (apply OAI.QAC.three_factor_transition <;> assumption)
    | (intros; apply OAI.QAC.three_factor_transition <;> assumption)
