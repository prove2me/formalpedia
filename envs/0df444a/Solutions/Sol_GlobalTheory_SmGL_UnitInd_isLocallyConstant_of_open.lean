-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isLocallyConstant_of_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:36.601071+00:00
-- url     : https://prove2.me/submissions/0823db91-146b-4b60-bef8-7bcbcc4520d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → Y}
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (h : ∀ x, ∀ u ∈ U, f (x * u) = f x) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' U) := hU.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (x := x) (by simpa using h1)] with y hy
  simpa using h x _ hy
end GlobalTheory.SmGL.UnitInd
