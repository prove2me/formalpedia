-- Prove2me | solution 1 for GlobalTheory.Square.Ratio.away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:19.852896+00:00
-- url     : https://prove2.me/submissions/7ce1e025-92cd-475f-9f0a-c695bebc431c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRatios
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_unit
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
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
open GlobalTheory GlobalTheory.Square GlobalTheory.Square.Ratio
open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)
namespace GlobalTheory.Square.Ratio
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {w : Pl K} {Qn : ℕ}
    (hQ : (Qn : 𝓞 K) ∉ w.asIdeal) {x : K} (h : IsAwayUnit Qn x) : x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', hd, hx⟩ := h
  have hQk : ∀ k, (Qn : 𝓞 K) ^ k ∉ w.asIdeal := fun k h => hQ (w.isPrime.mem_of_pow_mem k h)
  have ha : a ∉ w.asIdeal := fun h => hQk k' (Ideal.mem_of_dvd _ hd h)
  have ha0 : (a : K) ≠ 0 := by
    intro h; apply ha
    have : a = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  rw [← hx] at ha0
  have h1 := Formalism.DivisionValues.ReductionFirst.vw_unit w a ha
  have h2 := Formalism.DivisionValues.ReductionFirst.vw_unit w _ (hQk k)
  have e : (((Qn : 𝓞 K) ^ k : 𝓞 K) : K) = (Qn : K) ^ k := by simp
  rw [e] at h2
  rw [← hx, vw_mul w _ _ (left_ne_zero_of_mul ha0) (right_ne_zero_of_mul ha0), h2] at h1
  exact ⟨left_ne_zero_of_mul ha0, by simpa using h1⟩
end GlobalTheory.Square.Ratio
