-- Prove2me | solution 1 for GlobalTheory.SS.Height.od_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:14.127244+00:00
-- url     : https://prove2.me/submissions/aa0a012c-389c-475a-a4c3-40e37a8b8c1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Theorems.Thm_GlobalTheory_SS_Height_integral_value
import Theorems.Thm_GlobalTheory_SS_Height_od_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (Pl : Places k K)
namespace GlobalTheory.SS.Height
theorem _root_.solution (i) {X : Scheme.{0}} (b : Sp (Pl.O i) ⟶ X) (x : Sp K ⟶ X)
    (hb : spMap (Pl.O i).subtype ≫ b = x) (U : X.Opens) (h : b (closedPoint (Pl.O i)) ∈ U) (f : Γ(X, U)ˣ) :
    od Pl i (gm x (closedPoint K) U f) = 0 := by
  have hx : x (closedPoint K) ∈ U := hb ▸ (integral_value _ b U h).1
  refine (od_section Pl i b x hb U h f.val _ (gs_unit x _ U hx f)).2.2 ?_
  rw [X.basicOpen_of_isUnit f.isUnit]
  exact h
end GlobalTheory.SS.Height
