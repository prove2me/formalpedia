-- Prove2me | solution 1 for GlobalTheory.mean_fundamentalDomain_eq_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:09.551192+00:00
-- url     : https://prove2.me/submissions/ebee272b-dc5c-45d2-834d-e9e16ca771fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeanFundamentalDomainEqOfPeriodic
import Theorems.Thm_GlobalTheory_setIntegral_translate_of_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by
  intro n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  have : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩
  have hint : Integrable (Function.uncurry fun s t => g (s + t))
      ((volume.restrict D).prod (volume.restrict D')) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t := by
    simp_rw [setIntegral_translate_of_periodic L' D' g hD' hp']
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  have h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s := by
    have : ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s := fun t => by
      simp_rw [add_comm _ t]
      exact setIntegral_translate_of_periodic L D g hD hp t
    simp_rw [this]
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  rw [← h1, ← h2]
  exact integral_integral_swap hint
end GlobalTheory
