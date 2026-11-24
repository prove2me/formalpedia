-- Prove2me | solution 1 for GlobalTheory.Square.stepRatio_abs_vw_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:59.190747+00:00
-- url     : https://prove2.me/submissions/8a31b6f3-367d-4fdf-8f50-5fa6c2d3107f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
import Theorems.Thm_GlobalTheory_Square_stepRatio_vw_pow
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.Square
theorem _root_.solution (w : Pl K) {T : Type} (S : Finset T) (f : T → K) (r : T → ℝ)
    (h : ∀ v ∈ S, f v ≠ 0 ∧ |(vw w (f v) : ℝ)| ≤ r v) :
    |(vw w (∏ v ∈ S, f v) : ℝ)| ≤ ∑ v ∈ S, r v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := stepRatio_vw_pow w (one_ne_zero : (1 : K) ≠ 0) 0
    rw [pow_zero, Nat.cast_zero, zero_mul] at this
    rw [Finset.prod_empty, Finset.sum_empty, this]
    simp
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h1.1 (Finset.prod_ne_zero_iff.2 fun v hv => (h2 v hv).1)]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1.2 (ih h2))
end GlobalTheory.Square
