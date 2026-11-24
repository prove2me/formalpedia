-- Prove2me | solution 1 for GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:57.99134+00:00
-- url     : https://prove2.me/submissions/e0e22db9-0daa-4b0d-b486-74265d708296

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqOrEqNegOfPurelyImaginaryOfNormEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by
  intro E _ _ _ ξ ξ' τ h h' hn
  have key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    have h1 : τ (cc x) = (starRingEnd ℂ) (τ x) := IsCMField.complexEmbedding_complexConj E τ x
    rw [hx, map_neg] at h1
    have h2 := Complex.mul_conj' (τ x)
    rw [← h1] at h2
    rw [map_pow]
    push_cast
    linear_combination -h2
  have h3 : τ (ξ' ^ 2) = τ (ξ ^ 2) := by rw [key ξ h, key ξ' h', hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)
end GlobalTheory
