-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulCx.valH_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:42.139797+00:00
-- url     : https://prove2.me/submissions/9522ebb4-0a83-4549-a346-221bf01d8108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_appLE
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq


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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.KeyKa.KoszulCx
theorem _root_.solution (x : KeyIn R) (z : Pt x) (U : x.P.A.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ U) (c : R) :
    valT (T := R) z.left U (cst x.P.A.hom U c) = c := by
  have h0 : valT (T := R) z.left U (cst x.P.A.hom U c) =
      valT (T := R) z.left U ((x.P.A.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((EtBaseChange.valT_appLE (T := R) z.left x.P.A.hom (U := ⊤) le_top h _).trans ?_)
  have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
  erw [hz]
  rw [EtBaseChange.valT_eq _ _ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold EtBaseChange.valH
  erw [e3]
  simp
end GlobalTheory.KeyKa.KoszulCx
