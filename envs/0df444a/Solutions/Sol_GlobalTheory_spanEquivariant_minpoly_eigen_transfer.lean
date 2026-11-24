-- Prove2me | solution 1 for GlobalTheory.spanEquivariant_minpoly_eigen_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:14.313921+00:00
-- url     : https://prove2.me/submissions/57c8fd64-8eb6-4250-92f6-1cb2047881df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompat
import Theorems.Thm_GlobalTheory_spanEquivariant_aeval_map_apply
import Theorems.Thm_GlobalTheory_aeval_apply_of_apply_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  intro E _ _ V _ _ P hspan b T hT hadj
  constructor
  · apply LinearMap.ext_on_range hspan
    intro x
    rw [spanEquivariant_aeval_map_apply P b T hT, minpoly.aeval, zero_mul, map_zero, LinearMap.zero_apply]
  · intro σ a S hS y hy
    have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
    have ha : a ∈ Algebra.adjoin ℚ {b} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hadj]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨r, rfl⟩ := ha
    have hSeq : S = aeval T (r.map (algebraMap ℚ ℂ)) := by
      apply LinearMap.ext_on_range hspan
      intro x
      rw [hS, spanEquivariant_aeval_map_apply P b T hT]
      rfl
    rw [hSeq, aeval_apply_of_apply_eq_smul T (σ b) y hy, eval_map_algebraMap]
    congr 1
    exact Polynomial.aeval_algHom_apply σ.toRatAlgHom b r
end GlobalTheory
