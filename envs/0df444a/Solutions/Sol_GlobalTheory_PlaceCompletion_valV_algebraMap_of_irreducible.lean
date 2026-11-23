-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.valV_algebraMap_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.978802+00:00
-- url     : https://prove2.me/submissions/6ccd7904-650b-4807-aebf-a42b24fd4466

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution {v : V} (hv : Irreducible v) :
    valV V (algebraMap V K' v) = WithZero.exp (-1 : ℤ) := by
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer v).1 hv
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal V).intValuation_singleton hv.ne_zero hspan
end GlobalTheory.PlaceCompletion
