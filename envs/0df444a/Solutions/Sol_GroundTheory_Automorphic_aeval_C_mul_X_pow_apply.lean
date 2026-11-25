-- Prove2me | solution 1 for GroundTheory.Automorphic.aeval_C_mul_X_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:11.199466+00:00
-- url     : https://prove2.me/submissions/3d8cb8f6-b995-4779-9349-3de185b7b81a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}
omit [FiniteDimensional E V]
namespace GroundTheory.Automorphic
theorem _root_.solution (f : Module.End E V) (a : E) (k : ℕ) (x : V) :
    aeval f (C a * X ^ k) x = a • (f ^ k) x := by
  simp [Module.algebraMap_end_apply]
end GroundTheory.Automorphic
