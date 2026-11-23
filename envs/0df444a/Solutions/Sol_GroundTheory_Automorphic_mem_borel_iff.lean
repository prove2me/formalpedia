-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_borel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.921048+00:00
-- url     : https://prove2.me/submissions/6078d98c-86d9-4838-9ee0-3eaba242a157

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (g : GL (Fin n) k) :
    g ∈ borel n k ↔ ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) k) i j = 0 :=
  Iff.rfl
end GroundTheory.Automorphic
