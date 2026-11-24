-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.tau_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:10.861185+00:00
-- url     : https://prove2.me/submissions/4dc99fe6-3f4a-4cc0-ad8a-fc8854c2cf87

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
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]
end GlobalTheory.MatSqrtNearOne
