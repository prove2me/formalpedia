-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:19.457369+00:00
-- url     : https://prove2.me/submissions/dc6f2f1d-451d-49df-aa2f-fc4f362f5d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_locally_normal
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal


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
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    DifferentiableOn ℂ (fun p => ∑' i, c i * cexp (L i p)) U :=
  GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs)
end GlobalTheory.SW.ExpSum
