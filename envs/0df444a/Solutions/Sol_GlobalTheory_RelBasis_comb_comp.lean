-- Prove2me | solution 1 for GlobalTheory.RelBasis.comb_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:10.893966+00:00
-- url     : https://prove2.me/submissions/975a48fa-67f4-4976-b939-9d5eb563f5e1

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
import Theorems.Thm_GlobalTheory_RelBasis_gs_comp

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
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution {Z : Scheme.{0}} (b : Fin N → LB.Sec (pw L t)) (r : Z ⟶ Y) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (c : Fin N → Γ(T, W)) (z : Z) (i : L.ι) (h₁ : p₁ (r z) ∈ W) (h₂ : p₂ (r z) ∈ L.U i) :
    comb b (r ≫ p₁) (r ≫ p₂) W c z i = (r.stalkMap z).hom (comb b p₁ p₂ W c (r z) i) := by
  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, gs_comp r p₁ z W h₁]
  exact congrArg _ (gs_comp r p₂ z (L.U i) h₂ _)
end GlobalTheory.RelBasis
