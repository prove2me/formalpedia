-- Prove2me | solution 1 for GlobalTheory.SS.Slope.lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:30.339832+00:00
-- url     : https://prove2.me/submissions/803a7893-c955-46a1-b68a-b716dff2669c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
import Theorems.Thm_GlobalTheory_SS_Slope_weight_two
import Theorems.Thm_GlobalTheory_SS_Slope_exists_min

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Slope
open MvPowerSeries
variable {k : Type} [Field k]
namespace GlobalTheory.SS.Slope
theorem _root_.solution (m n : ℕ) (f g : MvPowerSeries (Fin 2) k) :
    weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) g ↔
      ∃ s : Fin 2 →₀ ℕ, coeff s f ≠ 0 ∧ ∀ t : Fin 2 →₀ ℕ, coeff t g ≠ 0 →
        m * s 0 + n * s 1 < m * t 0 + n * t 1 := by
  constructor
  · intro h
    have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs, hs'⟩ := exists_min ![m, n] f hf
    refine ⟨s, hs, fun t ht => ?_⟩
    have := lt_of_lt_of_le (hs' ▸ h) (weightedOrder_le ![m, n] ht)
    rw [← weight_two, ← weight_two]
    exact_mod_cast this
  · rintro ⟨s, hs, h⟩
    refine lt_of_le_of_lt (weightedOrder_le _ hs) ?_
    by_cases hg : g = 0
    · subst hg
      simp
    · obtain ⟨t, ht, ht'⟩ := exists_min ![m, n] g hg
      rw [← ht', weight_two, weight_two]
      exact_mod_cast h t ht
end GlobalTheory.SS.Slope
