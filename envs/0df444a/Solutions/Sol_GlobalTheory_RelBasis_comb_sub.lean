-- Prove2me | solution 1 for GlobalTheory.RelBasis.comb_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:55:15.442015+00:00
-- url     : https://prove2.me/submissions/95a0f4b4-5488-42d1-b911-405f682bd0f6

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisOfAffineOpens
import Theorems.Thm_GlobalTheory_RelBasis_gs_eq_gsHom


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
theorem _root_.solution (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {W : T.Opens}
    (c c' : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ W) :
    comb b p₁ p₂ W (c - c') y i = comb b p₁ p₂ W c y i - comb b p₁ p₂ W c' y i := by
  unfold comb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gs_eq_gsHom p₁ y W h, Pi.sub_apply, map_sub, sub_mul]
end GlobalTheory.RelBasis
