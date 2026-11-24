-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.tau_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:11.536853+00:00
-- url     : https://prove2.me/submissions/3153c33e-7dfb-41c2-8ad2-21ced7f2a368

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
theorem _root_.solution (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]
end GlobalTheory.MatSqrtNearOne
