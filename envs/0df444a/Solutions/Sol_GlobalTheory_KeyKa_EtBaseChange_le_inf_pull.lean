-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.le_inf_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:41.835369+00:00
-- url     : https://prove2.me/submissions/b1f519a6-23e8-43fa-afee-5269919e7247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution {T : Type} [CommRing T] (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    ⊤ ≤ p ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') :=
  fun _ hy => ⟨mem_pull.2 (h hy), h' hy⟩
end GlobalTheory.KeyKa.EtBaseChange
