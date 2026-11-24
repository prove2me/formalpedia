-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.exists_finset_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:22:54.251639+00:00
-- url     : https://prove2.me/submissions/156fb702-a62e-4321-aa88-e29f6bc7e039

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution {L : Type} {f₀ : L → Fin g → ℂ} {U : Set (L → Fin g → ℂ)} (hU : U ∈ nhds f₀) :
    ∃ (s : Finset L) (ε : ℝ), 0 < ε ∧ ∀ f, (∀ x ∈ s, ‖f x - f₀ x‖ < ε) → f ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, t, ht, hs⟩ := hU
  have : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ x ∈ s, Metric.ball (f₀ x) ε ⊆ t x := by
    rw [Filter.eventually_all_finset]
    intro x _
    exact (eventually_ball_subset (ht x)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨s, ε, h2, fun f hf => hs fun x hx => h1 x hx (by simpa [dist_eq_norm] using hf x hx)⟩
end GlobalTheory.PeriodCoord
