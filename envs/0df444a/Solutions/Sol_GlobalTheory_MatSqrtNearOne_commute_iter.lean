-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.commute_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:12.844982+00:00
-- url     : https://prove2.me/submissions/4d859039-99bf-489c-9084-2ceffc7cc722

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}
namespace GlobalTheory.MatSqrtNearOne
theorem _root_.solution {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  | 0 => Commute.zero_right a
  | k + 1 => h.sub_right ((solution h k).mul_right (solution h k))
end GlobalTheory.MatSqrtNearOne
