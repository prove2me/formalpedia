-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.twist_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:41.221168+00:00
-- url     : https://prove2.me/submissions/49391955-862f-42b8-bb1f-5a42ac662b4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {E : B.A} (hE : E * E = E) {x : B.A} (hx : IsUnit x) : IsUnit (x * E + (1 - E)) := by
  obtain ⟨u, rfl⟩ := hx
  refine isUnit_iff_exists_inv.2 ⟨((u⁻¹ : B.Aˣ) : B.A) * E + (1 - E), ?_⟩
  rw [twist_mul B hE, Units.mul_inv, one_mul]; ring
end GlobalTheory.UnitLemma.Desc
