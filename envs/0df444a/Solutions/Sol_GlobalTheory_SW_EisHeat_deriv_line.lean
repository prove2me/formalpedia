-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.deriv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:32:43.005537+00:00
-- url     : https://prove2.me/submissions/d3d2b746-aced-492e-b11e-0f79253eeb5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
omit [FiniteDimensional ℂ X]
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : X → V} {p : X}
    (hf : DifferentiableAt ℂ f p) (v : X) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by
  have h : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 h (by simp)
end GlobalTheory.SW.EisHeat
