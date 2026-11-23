-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.isOpen_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:40.849538+00:00
-- url     : https://prove2.me/submissions/a28a30ca-4f34-47be-a10c-813b2c30c90d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_imH_isHermitian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_posDef_eventually


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
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N => imH (q.1 τ)) (fun i j => ?_)
    (fun q => imH_isHermitian _) p (hp τ)
  change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
    (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i))
  fun_prop
end GlobalTheory.SW.ExpSum
