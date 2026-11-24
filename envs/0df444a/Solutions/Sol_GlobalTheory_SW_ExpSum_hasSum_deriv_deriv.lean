-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.hasSum_deriv_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:42.624802+00:00
-- url     : https://prove2.me/submissions/e752c085-783b-459f-9e23-0d2fe67f62a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_hasSum_deriv

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
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (v w : V)
    (hp : ∀ s : ℂ, p + s • v ∈ U) :
    HasSum (fun i => c i * L i w * L i v * cexp (L i p))
      (deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' i, c i * cexp (L i (p + s • v + t • w))) 0) 0) := by
  have h := hasSum_deriv hU (fun i => c i * L i w) L
    (fun q hq => summable_norm_iff.2 (hasSum_deriv hU c L hs hq w).summable)
    (p := p) (by simpa using hp 0) v
  convert h using 3 with s
  exact (hasSum_deriv hU c L hs (hp s) w).tsum_eq.symm
end GlobalTheory.SW.ExpSum
