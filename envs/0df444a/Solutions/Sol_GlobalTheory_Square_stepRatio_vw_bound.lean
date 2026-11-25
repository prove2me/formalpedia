-- Prove2me | solution 1 for GlobalTheory.Square.stepRatio_vw_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:54.624691+00:00
-- url     : https://prove2.me/submissions/49fbf768-bbe1-47be-a3df-6fd671ca9e21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_StepRatioAbsVwProd
import Theorems.Thm_GlobalTheory_Square_stepRatio_vw_of_dvd
import Theorems.Thm_GlobalTheory_Square_stepRatio_abs_vw_prod
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_GlobalTheory_Square_IsAwayUnit_ne_zero_and_vw


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ),
    (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (T : Type) (S0 : Finset T) (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → ∀ u1 u0 : ℂ,
    StepRatio σ₀ Qn S0 cc qq u1 u0 → ∃ t : K, t ≠ 0 ∧ u1 = σ₀ t * u0 ∧
      |(vw w t : ℝ)| ≤ 2 * ∑ v ∈ S0, (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by
  intro K _ _ _ σ₀ w Qn hQ T S0 cc qq hq u1 u0 h
  obtain ⟨b, g, g', hb, hg, hu⟩ := h
  obtain ⟨hb0, hbv⟩ := hb.ne_zero_and_vw w hQ
  have key : ∀ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 ∧
      |(vw w ((g v : K) / (g' v : K)) : ℝ)| ≤ 2 * ((cc v : ℝ) * (vw w (qq v : K) : ℝ)) := by
    intro v hv
    obtain ⟨a0, a1, a2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).1
    obtain ⟨b0, b1, b2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).2
    refine ⟨div_ne_zero a0 b0, ?_⟩
    rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ a0 (inv_ne_zero b0), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    have a1' : (0 : ℝ) ≤ (vw w (g v : K) : ℝ) := by exact_mod_cast a1
    have a2' : (vw w (g v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast a2
    have b1' : (0 : ℝ) ≤ (vw w (g' v : K) : ℝ) := by exact_mod_cast b1
    have b2' : (vw w (g' v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast b2
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hp : ∏ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (key v hv).1
  refine ⟨_, mul_ne_zero hb0 hp, hu, ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hb0 hp, hbv, zero_add, Finset.mul_sum]
  exact stepRatio_abs_vw_prod w S0 _ _ key
end GlobalTheory.Square
