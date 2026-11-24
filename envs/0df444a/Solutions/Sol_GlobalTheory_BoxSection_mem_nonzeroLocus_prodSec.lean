-- Prove2me | solution 1 for GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:27.987708+00:00
-- url     : https://prove2.me/submissions/d6157ebe-9065-43d6-aa06-f861000affab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
import Theorems.Thm_GlobalTheory_BoxSection_mem_basicOpen_prod

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (t : K → L.Sec) (y : Y) (h : ∀ i, φ i y ∈ Out.nonzeroLocus (t i)) :
    y ∈ Out.nonzeroLocus (prodSec L φ t) := by
  choose k hk using fun i => TopologicalSpace.Opens.mem_iSup.1 (h i)
  have hy : y ∈ LB.wchart L φ k := Set.mem_iInter.2 fun i => X.basicOpen_le _ (hk i)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_basicOpen_prod _ hy fun i => ?_⟩
  exact (Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ k i) _).ge ⟨hy, hk i⟩
end GlobalTheory.BoxSection
