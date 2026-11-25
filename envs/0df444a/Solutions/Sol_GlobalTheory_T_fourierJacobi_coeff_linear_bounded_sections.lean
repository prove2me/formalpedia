-- Prove2me | solution 1 for GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:19.084998+00:00
-- url     : https://prove2.me/submissions/23fe23bf-a152-49b0-864d-7377e4bf07fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FourierJacobiCoeffLinearBoundedSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FourierJacobiCoeffLinearBoundedSectionsStatement
import Theorems.Thm_GlobalTheory_fj_eq_sum_of_eqOn_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℕ) (a : Fin m → ℂ) (Q : Fin m → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (Q i)) → (∀ x ∈ X.dom, f x = ∑ i, a i * Q i x) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν f x = ∑ i, a i * X.fj la ξ ν (Q i) x := by
  first | exact @GlobalTheory.fj_eq_sum_of_eqOn_dom | exact GlobalTheory.fj_eq_sum_of_eqOn_dom | (intros; apply GlobalTheory.fj_eq_sum_of_eqOn_dom <;> assumption)
end _root_.GlobalTheory.T
