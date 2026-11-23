-- Prove2me | solution 1 for GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:22.497672+00:00
-- url     : https://prove2.me/submissions/7de3eb95-6b26-4ea9-9944-829668fb74c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AppellHumbertTrivial
namespace GlobalTheory.AppellHumbertTrivial
namespace _root_.GlobalTheory.AppellHumbertTrivial
theorem _root_.solution {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {F : Type} [NormedAddCommGroup F]
    (φ : (Fin g → ℂ) → F) (hφ : Continuous φ)
    (hp : ∀ (l : Λ) z, φ (z + l) = φ z) : Bornology.IsBounded (Set.range φ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  exact (IsZLattice.isCompact_range_of_periodic Λ φ hφ
    (fun z w hw => hp ⟨w, hw⟩ z)).isBounded
end _root_.GlobalTheory.AppellHumbertTrivial
end GlobalTheory.AppellHumbertTrivial
