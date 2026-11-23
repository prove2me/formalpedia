-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:35.086959+00:00
-- url     : https://prove2.me/submissions/c4ae5722-c102-49ca-9b14-6a29696ba4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_le_one
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_lt_one_iff

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
theorem _root_.solution {v : V} (hv : IsUnit v) : valV V (algebraMap V K' v) = 1 := by
  refine le_antisymm (valV_algebraMap_le_one v) (not_lt.1 fun hlt => ?_)
  have hm := (valV_algebraMap_lt_one_iff v).1 hlt
  exact (IsLocalRing.mem_maximalIdeal v).1 hm hv
end GlobalTheory.PlaceCompletion
