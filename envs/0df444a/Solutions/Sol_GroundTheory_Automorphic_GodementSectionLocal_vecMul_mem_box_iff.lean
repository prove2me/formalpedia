-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_box_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:10.820959+00:00
-- url     : https://prove2.me/submissions/cbd3d576-dbfe-44ff-a204-8aa861bf675a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_mem_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (n : ℤ)
    (x : Fin 2 → F) : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ box F n ↔ x ∈ box F n := by
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  refine ⟨fun h ↦ ?_, vecMul_mem_box hk1⟩
  have := vecMul_mem_box (k := k⁻¹) hk2 h
  rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at this
end GroundTheory.Automorphic.GodementSectionLocal
