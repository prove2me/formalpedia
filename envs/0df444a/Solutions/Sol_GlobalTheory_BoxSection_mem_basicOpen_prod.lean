-- Prove2me | solution 1 for GlobalTheory.BoxSection.mem_basicOpen_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:55.080317+00:00
-- url     : https://prove2.me/submissions/0ac1aa57-8fc0-417f-a18d-163c164cf9ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec

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
open GlobalTheory GlobalTheory.BoxSection
namespace GlobalTheory.BoxSection
theorem _root_.solution {Y : Scheme.{0}} {K : Type} [Fintype K] {W : Y.Opens} (a : K → Γ(Y, W))
    {y : Y} (hy : y ∈ W) (h : ∀ i, y ∈ Y.basicOpen (a i)) : y ∈ Y.basicOpen (∏ i, a i) := by
  rw [Scheme.mem_basicOpen _ _ y hy, map_prod]
  exact IsUnit.prod_univ_iff.2 fun i => (Scheme.mem_basicOpen _ _ y hy).1 (h i)
end GlobalTheory.BoxSection
