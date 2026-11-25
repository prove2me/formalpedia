-- Prove2me | solution 1 for GlobalTheory.FlagSecProbe.isSec_congr_on_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:05.833988+00:00
-- url     : https://prove2.me/submissions/2791c546-359d-4d18-8cc1-8048193db3f1

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
theorem _root_.solution (X : Data E (r + 1)) (la : Wt X.Ψ (r + 1))
    (P : Frame X.Ψ (r + 1) → ℂ) (hP : X.IsSec la P) (Q : Frame X.Ψ (r + 1) → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ (r + 1), rmul x b ∈ X.dom)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, lact γ x ∈ X.dom)
    (hQ : ∀ x ∈ X.dom, Q x = P x) : X.IsSec la Q :=
  ⟨hP.1.congr hQ, fun x hx b hb => by rw [hQ _ (hB x hx b hb), hQ x hx, hP.2.1 x hx b hb],
    fun γ hγ x hx => by rw [hQ _ (hΓ γ hγ x hx), hQ x hx, hP.2.2 γ hγ x hx]⟩
end GlobalTheory.FlagSecProbe
