-- Prove2me | solution 1 for GlobalTheory.FlagSecProbe.pnorm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:19.882401+00:00
-- url     : https://prove2.me/submissions/1c539879-3b29-4ce0-97e3-35c1ee6afd4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_WeightEqZeroOfOneIsSec
import Theorems.Thm_GlobalTheory_FlagSecProbe_dmin_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open GlobalTheory GlobalTheory.FlagSecProbe
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagSecProbe
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la P x = 0 ↔ P x = 0 := by
  unfold Data.pnorm
  have : (∏ τ, ∏ i : Fin r,
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2
      (div_ne_zero (dmin_ne_zero X hx τ _) (dmin_ne_zero X hx τ _))) _).ne'
  rw [mul_eq_zero, or_iff_left this, norm_eq_zero]
end GlobalTheory.FlagSecProbe
