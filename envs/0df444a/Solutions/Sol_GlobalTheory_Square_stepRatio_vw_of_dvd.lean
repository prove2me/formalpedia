-- Prove2me | solution 1 for GlobalTheory.Square.stepRatio_vw_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:59.804748+00:00
-- url     : https://prove2.me/submissions/82bd7444-baed-43f0-a108-60aa6f4ebd54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
import Theorems.Thm_GlobalTheory_Square_stepRatio_vw_pow
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_int_nonneg
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg
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
theorem _root_.solution (w : Pl K) {q c : ℕ} (hq : 0 < q) {g : 𝓞 K} (hg : g ∣ (q : 𝓞 K) ^ c) :
    (g : K) ≠ 0 ∧ 0 ≤ vw w (g : K) ∧ vw w (g : K) ≤ c * vw w (q : K) := by
  obtain ⟨b, hb⟩ := hg
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h : (q : K) ^ c = (g : K) * (b : K) := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hb
    simpa using this
  have hne : (g : K) * (b : K) ≠ 0 := h ▸ pow_ne_zero c hq0
  have hg0 := left_ne_zero_of_mul hne
  have hb0 := right_ne_zero_of_mul hne
  refine ⟨hg0, Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w g, ?_⟩
  rw [← stepRatio_vw_pow w hq0, h, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hg0 hb0]
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w b
  omega
end GlobalTheory.Square
