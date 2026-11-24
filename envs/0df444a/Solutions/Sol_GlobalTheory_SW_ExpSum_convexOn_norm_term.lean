-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.convexOn_norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:04.748804+00:00
-- url     : https://prove2.me/submissions/2fd5a552-cdc7-499d-9073-878694858ce1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}
omit [FiniteDimensional ℂ V]
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (c : ℂ) (L : V →L[ℂ] ℂ) :
    ConvexOn ℝ Set.univ fun p => ‖c * cexp (L p)‖ := by
  have h : ConvexOn ℝ Set.univ fun p => Real.exp ((L p).re) := by
    have := convexOn_exp.comp_linearMap
      (Complex.reLm ∘ₗ (L.toLinearMap.restrictScalars ℝ))
    exact this
  simpa only [norm_mul, Complex.norm_exp, smul_eq_mul] using h.smul (norm_nonneg c)
end GlobalTheory.SW.ExpSum
