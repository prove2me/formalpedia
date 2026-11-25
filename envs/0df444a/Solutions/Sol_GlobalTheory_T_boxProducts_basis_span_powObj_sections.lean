-- Prove2me | solution 1 for GlobalTheory.T.boxProducts_basis_span_powObj_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:44.157295+00:00
-- url     : https://prove2.me/submissions/b00fd6ed-85f8-413a-bee1-29c65c82f6ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSections
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSectionsStatement
import Theorems.Thm_GlobalTheory_BoxSpan_boxProducts_span


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  first | exact @GlobalTheory.BoxSpan.boxProducts_span | exact GlobalTheory.BoxSpan.boxProducts_span | (intros; apply GlobalTheory.BoxSpan.boxProducts_span <;> assumption)
end _root_.GlobalTheory.T
