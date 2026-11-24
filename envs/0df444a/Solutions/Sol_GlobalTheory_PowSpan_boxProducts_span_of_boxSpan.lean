-- Prove2me | solution 1 for GlobalTheory.PowSpan.boxProducts_span_of_boxSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:09.566257+00:00
-- url     : https://prove2.me/submissions/6572d11f-b3b9-49a9-abcf-4436737449d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsSpanExternalPowersOfBoxSpan
import Theorems.Thm_GlobalTheory_PowSpan_gs_cst
import Theorems.Thm_GlobalTheory_PowSpan_span_ev

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
open GlobalTheory GlobalTheory.PowSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
namespace GlobalTheory.PowSpan
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  intro R _ A L t N b hL hb n s
  obtain ⟨q, hq⟩ := span_ev A L t N b hL hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]
end GlobalTheory.PowSpan
