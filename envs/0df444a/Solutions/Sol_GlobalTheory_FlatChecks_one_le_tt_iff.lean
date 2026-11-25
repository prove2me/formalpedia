-- Prove2me | solution 1 for GlobalTheory.FlatChecks.one_le_tt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:04.456831+00:00
-- url     : https://prove2.me/submissions/7f6fcb7e-dc5e-4776-b708-3b291a1543a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlatChecks
theorem _root_.solution (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    1 ≤ X.tt ξ x τ ↔ 0 < X.c τ * X.maj x τ (Data.emb τ.1 ξ) ∧ X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1 := by
  unfold Data.tt
  generalize X.c τ * X.maj x τ (Data.emb τ.1 ξ) = h
  constructor
  · intro h1
    have hp : 0 < h := by
      by_contra hn
      have : 1 / h ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one (not_lt.1 hn)
      linarith
    exact ⟨hp, by rwa [le_div_iff₀ hp, one_mul] at h1⟩
  · rintro ⟨hp, h1⟩
    rwa [le_div_iff₀ hp, one_mul]
end GlobalTheory.FlatChecks
