-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.tau_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:10.035944+00:00
-- url     : https://prove2.me/submissions/80e61336-b436-472c-b70e-f35b5c41bfe6

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
theorem _root_.solution (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A + B).map σ)ᵀ = (A.map σ)ᵀ + (B.map σ)ᵀ := by
  ext i j; simp
end GlobalTheory.MatSqrtNearOne
