-- Prove2me | solution 1 for GlobalTheory.exists_factor_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:59.838846+00:00
-- url     : https://prove2.me/submissions/7088982e-af19-4641-8189-9438a24ea8ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {X : Scheme.{0}}
    (a : Spec (.of K) ⟶ X) {x : X} (hx : a (IsLocalRing.closedPoint K) = x) :
    ∃ φ : X.residueField x ⟶ .of K, Spec.map φ ≫ X.fromSpecResidueField x = a := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X a⟩
end GlobalTheory
