-- Prove2me | solution 1 for GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:45.642707+00:00
-- url     : https://prove2.me/submissions/bb701f2d-e231-49fe-8456-ccb8ce9814c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AeEqOfDenseOfLocalSqBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AeEqOfDenseOfLocalSqBoundStatement
import Theorems.Thm_GlobalTheory_ae_eq_of_dense_of_local_sq_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  first | exact @GlobalTheory.ae_eq_of_dense_of_local_sq_bound | exact GlobalTheory.ae_eq_of_dense_of_local_sq_bound | (intros; apply GlobalTheory.ae_eq_of_dense_of_local_sq_bound <;> assumption)
end _root_.GlobalTheory.T
