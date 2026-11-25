-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.unifPow_smul_unifPow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:46.019507+00:00
-- url     : https://prove2.me/submissions/42774f5f-b416-46b2-b6ae-fff797fcf301

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal

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
theorem _root_.solution (k : ℤ) (x : Fin 2 → F) :
    ((unifPow k : Fˣ) : F) • ((unifPow (-k) : Fˣ) : F) • x = x := by
  have h : unifPow k * unifPow (-k) = (1 : Fˣ) := by
    rw [unifPow, unifPow, _root_.zpow_neg, mul_inv_cancel]
  rw [smul_smul, ← Units.val_mul, h, Units.val_one, one_smul]
end GroundTheory.Automorphic.GodementSectionLocal
