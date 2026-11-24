-- Prove2me | solution 1 for GlobalTheory.Conv.eventually_iff_eTwoPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:17.126847+00:00
-- url     : https://prove2.me/submissions/a0343588-0f15-420d-89e2-c4fbfdc081fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_cuspRadius_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → p (eTwoPi w) := by
  rw [eventually_iff_exists_puncturedDisc]
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨T, rfl⟩ := exists_cuspRadius_eq hε
    exact ⟨T, fun w hw => h _ (eTwoPi_mem_puncturedDisc.2 hw)⟩
  · rintro ⟨T, h⟩
    refine ⟨cuspRadius T, cuspRadius_pos T, fun v hv => ?_⟩
    obtain ⟨w, rfl⟩ := exists_eTwoPi_eq (mem_puncturedDisc.1 hv).1
    exact h w (eTwoPi_mem_puncturedDisc.1 hv)
end GlobalTheory.Conv
