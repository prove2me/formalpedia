-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.stabilizer_standard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:49.91606+00:00
-- url     : https://prove2.me/submissions/edbfae1e-cce2-4ef7-8015-1fe1d1758231

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution :
    MulAction.stabilizer (GL (Fin n) F) (standard F n) = integralGL F n := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_standard_eq_iff]
end GroundTheory.Automorphic.GLnLocal
