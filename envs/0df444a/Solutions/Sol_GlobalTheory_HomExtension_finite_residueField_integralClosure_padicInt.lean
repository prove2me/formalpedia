-- Prove2me | solution 1 for GlobalTheory.HomExtension.finite_residueField_integralClosure_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:22:23.94083+00:00
-- url     : https://prove2.me/submissions/4c63a632-5d0d-4c86-b274-a7c8645d7dd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldIntegralClosurePadicInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_isLocalHom


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
open GlobalTheory
open GlobalTheory.HomExtension
namespace GlobalTheory.HomExtension
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] :
    Finite (IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[p] ℚ_[p] L
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[p] L
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[p])
end GlobalTheory.HomExtension
