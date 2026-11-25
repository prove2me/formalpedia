-- Prove2me | solution 1 for GlobalTheory.BoxSpan.boxProducts_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:15.040496+00:00
-- url     : https://prove2.me/submissions/e6e31c24-9442-496c-82d2-8ae1b184bcbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSections
import Theorems.Thm_GlobalTheory_BoxSpan_gs_cst
import Theorems.Thm_GlobalTheory_BoxSpan_span_ev

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
open GlobalTheory GlobalTheory.BoxSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
namespace GlobalTheory.BoxSpan
theorem _root_.solution : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  intro K _ x m N b hb n s
  obtain ⟨q, hq⟩ := span_ev K x m N b hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]
end GlobalTheory.BoxSpan
