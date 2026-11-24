-- Prove2me | solution 1 for GlobalTheory.setIntegral_translate_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:43.59726+00:00
-- url     : https://prove2.me/submissions/cfed3ecc-afb9-4122-8fba-2f6aa88b675a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeanFundamentalDomainEqOfPeriodic

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
theorem _root_.solution {n : Type} [Fintype n] (L : AddSubgroup (n → ℝ))
    [Countable L] (D : Set (n → ℝ)) (g : (n → ℝ) → ℂ)
    (hD : IsAddFundamentalDomain L D volume) (hp : ∀ p ∈ L, ∀ s, g (s + p) = g s)
    (s : n → ℝ) : ∫ t in D, g (s + t) = ∫ t in D, g t := by
  have hsD : IsAddFundamentalDomain L (s +ᵥ D) volume := hD.vadd_of_comm s
  have himg : (fun t => s + t) '' D = s +ᵥ D := by
    change (fun t => s +ᵥ t) '' D = s +ᵥ D
    exact Set.image_vadd
  rw [← (measurePreserving_add_left volume s).setIntegral_image_emb
    (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]
  refine hsD.setIntegral_eq hD (fun p x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hp p p.2 x
end GlobalTheory
