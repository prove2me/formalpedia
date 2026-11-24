-- Prove2me | solution 1 for GlobalTheory.upperFactor_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:25.927693+00:00
-- url     : https://prove2.me/submissions/34758108-d6ec-4297-92d2-423ca824be56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    (upperFactor i j x).det = -1 := by
  have hij : i ≠ j := ne_of_gt hji
  rw [upperFactor, det_mul, det_transvection_of_ne j i (ne_of_lt hji), det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  simp [hx]
end GlobalTheory
