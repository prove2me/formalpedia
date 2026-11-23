-- Prove2me | solution 1 for GroundTheory.Automorphic.borel_diag_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:53.213803+00:00
-- url     : https://prove2.me/submissions/135f3331-dc43-4838-8876-27012d8eb095

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
theorem _root_.solution {b : GL (Fin n) k} (hb : b ∈ borel n k) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have hdet : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  rw [det_of_isUpperTriangular hb] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
end GroundTheory.Automorphic
