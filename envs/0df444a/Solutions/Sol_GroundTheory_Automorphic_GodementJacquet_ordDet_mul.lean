-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.ordDet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:18.123304+00:00
-- url     : https://prove2.me/submissions/c4b23bdb-4e25-40b8-8dd8-9685e7f005bc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_det_ne_zero
import Theorems.Thm_GroundTheory_LocalField_ord_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (g h : GL (Fin n) F) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, ordDet, ordDet, Units.val_mul, Matrix.det_mul,
    LocalField.ord_mul (det_ne_zero g) (det_ne_zero h)]
end GroundTheory.Automorphic.GodementJacquet
