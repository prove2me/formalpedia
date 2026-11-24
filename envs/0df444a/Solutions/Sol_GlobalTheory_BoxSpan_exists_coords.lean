-- Prove2me | solution 1 for GlobalTheory.BoxSpan.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:35:28.230651+00:00
-- url     : https://prove2.me/submissions/f70551f5-a099-4848-b2c3-6024052b1190

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
import Theorems.Thm_GlobalTheory_BoxSpan_gs_sum
import Theorems.Thm_GlobalTheory_BoxSpan_exists_sec_pw

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
theorem _root_.solution (x : KeyIn R) {m N : ℕ} (b : Fin N → RR x m) (hb : IsBasis x b)
    (a : LB.Sec (LB.LinComb x.P.L (K := PUnit) (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)))) :
    ∃ c : Fin N → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) J, Good x.P.L z J →
      sval a r z J = ∑ k, ev (r ≫ x.P.A.hom) z (c k) * gs r z (x.P.L.U (J r)) ((b k).f (J r)) := by
  obtain ⟨a', ha⟩ := exists_sec_pw x.P.L m a
  obtain ⟨c, hc, -⟩ := hb a'
  refine ⟨c, fun Z r z J hJ => (ha Z r z J hJ).trans ((congrArg (gs r z _) (hc (J r))).trans
    ((gs_sum _ r z _ (hJ r) _).trans (Finset.sum_congr rfl fun k _ => ?_)))⟩
  exact (gs_mul r z _ (hJ r) _ _).trans (congrArg (· * _) (gs_cst _ r z _ (hJ r) _))
end GlobalTheory.BoxSpan
