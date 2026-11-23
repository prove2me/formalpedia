-- Prove2me | solution 1 for GlobalTheory.KeyPow.ClauseH.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:28.751327+00:00
-- url     : https://prove2.me/submissions/819126ef-289f-4830-9bb1-92e7cf6d39c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
namespace ClauseH
theorem _root_.solution {R : Type} [CommRing R] {N : ℕ → ℕ} {g₀ g₁ : ℕ} {κ : KeyIn R → Rˣ}
    (h : ClauseH R N g₀ κ) (hg : g₀ ≤ g₁) : ClauseH R N g₁ κ := by
  intro P hg' rig hr th hth v hv th' hth' v' hv' a M hP
  exact h P hg' rig hr th hth v hv th' hth' v' hv' a M (hg.trans hP)
end ClauseH
end GlobalTheory.KeyPow
