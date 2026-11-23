-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:08.384254+00:00
-- url     : https://prove2.me/submissions/53465580-2a00-4fc3-bdcb-f1b66810aece

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
theorem _root_.solution {x : K'} (hx : valV V x ≤ 1) :
    ∃ v : V, algebraMap V K' v = x := by
  have honly : ∀ w : HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := fun w =>
    HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
  unfold valV at hx
  obtain ⟨v, hv⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V) (K := K') x
    (fun w => by rw [honly w]; exact hx)
  exact ⟨v, hv⟩
end GlobalTheory.PlaceCompletion
