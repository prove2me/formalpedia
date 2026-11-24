-- Prove2me | solution 1 for GlobalTheory.SW.TwistMove.std_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:34.908495+00:00
-- url     : https://prove2.me/submissions/c79595c0-4009-4c8d-90fa-836be9b3eb23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistMove
theorem _root_.solution : (stdL E N).toAddSubgroup =
    AddSubgroup.closure (Set.range (Pi.basis fun _ : Fin N => integralBasis E)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Base.mem_stdL,
    Module.Basis.mem_span_iff_repr_mem, Sigma.forall]
  refine forall_congr' fun a => ?_
  simp only [Pi.basis_repr]
  rw [← Module.Basis.mem_span_iff_repr_mem, mem_span_integralBasis]
  exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩
end GlobalTheory.SW.TwistMove
