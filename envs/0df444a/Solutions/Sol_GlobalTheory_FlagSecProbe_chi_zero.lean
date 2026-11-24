-- Prove2me | solution 1 for GlobalTheory.FlagSecProbe.chi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:39.92961+00:00
-- url     : https://prove2.me/submissions/34919506-1536-4326-8239-869439e3126f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_WeightEqZeroOfOneIsSec

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
theorem _root_.solution (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h0 : X.χ 0 γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  exact (mul_right_eq_self₀.1 h1.symm).resolve_right h0
end GlobalTheory.FlagSecProbe
