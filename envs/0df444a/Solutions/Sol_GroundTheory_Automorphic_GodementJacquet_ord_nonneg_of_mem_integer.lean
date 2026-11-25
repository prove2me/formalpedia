-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.ord_nonneg_of_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:13.47051+00:00
-- url     : https://prove2.me/submissions/5c256b2e-5ae6-4317-8d80-125110666121

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe

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
theorem _root_.solution {x : F} (hx : x ∈ 𝒪[F]) (h0 : x ≠ 0) : 0 ≤ LocalField.ord x :=
  (LocalField.mem_valBall_iff_le_ord h0).1 (LocalField.mem_valBall_zero_iff.2 hx)
end GroundTheory.Automorphic.GodementJacquet
