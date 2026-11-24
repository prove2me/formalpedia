-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.fst_valT_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:27.703679+00:00
-- url     : https://prove2.me/submissions/6a0d3428-ba02-48bc-ac5b-75c4df3bf39c

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
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_spMap
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_fst_comp_translate
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_le

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
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) {U : G.left.Opens}
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) (a : Γ(G.left, U)) :
    (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * v).left U a).fst = valT (T := R) z.left U a := by
  have := valT_spMap (TrivSqZeroExt.fstHom R R R).toRingHom ((toUnit (epsR R) ≫ z) * v).left
    (translate_le z v hv h) a
  rw [fst_comp_translate z v hv] at this
  exact this.symm
end GlobalTheory.KeyKa.EtBaseChange
