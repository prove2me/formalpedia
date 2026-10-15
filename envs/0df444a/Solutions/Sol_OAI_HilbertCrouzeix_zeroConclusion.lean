-- Prove2me | solution 1 for OAI.HilbertCrouzeix.zeroConclusion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:13:18.682436+00:00
-- url     : https://prove2.me/submissions/3345c475-280c-4727-a082-69ae91ab1408

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/Calculus.lean:L84-L99
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HilbertCrouzeix.zeroConclusion.
-- The statement is the platform stub (Theorems.Thm_OAI_HilbertCrouzeix_zeroConclusion) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange

-- ---- inline helpers from OAI.Analysis.HilbertCrouzeix.Calculus ----
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section TrivialSpace
omit [CompleteSpace H]

theorem numericalRange_eq_empty [Subsingleton H] (A : H →L[ℂ] H) :
    numericalRange A = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨x, hx, h⟩
  have hx0 : x = 0 := Subsingleton.elim _ _
  simp [hx0] at hx

theorem amplification_eq_zero [Subsingleton H] (m : ℕ) (x : Amplification H m) :
    x = 0 := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq continuous_id continuous_const) ?_
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, UniformSpace.Completion.coe_zero]

theorem amplifiedOperator_eq_zero [Subsingleton H] (m : ℕ)
    (T : Amplification H m →L[ℂ] Amplification H m) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact amplification_eq_zero m (T x)

end TrivialSpace

end HilbertCrouzeix

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.HilbertCrouzeix
open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

theorem solution [Subsingleton H] (A : H →L[ℂ] H) : ZeroConclusion A := by
  have hW := numericalRange_eq_empty A
  refine ⟨hW, ?_, ?_⟩
  · intro m F
    simp [hW]
  · intro m hm
    refine ⟨amplifiedOperator_eq_zero m, ?_, ?_, ?_⟩
    · intro d B
      have hP := amplifiedOperator_eq_zero m (polynomialEval A B)
      exact ⟨hP, by simp only [hP, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩
    · intro U F
      have hF := amplifiedOperator_eq_zero m (holomorphicEval A U F)
      exact ⟨hF, by simp only [hF, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩
    · intro R
      have hR := amplifiedOperator_eq_zero m (rationalEval A R)
      exact ⟨hR, by simp only [hR, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩
