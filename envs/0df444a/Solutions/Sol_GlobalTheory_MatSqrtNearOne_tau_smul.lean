-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.tau_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:12.174074+00:00
-- url     : https://prove2.me/submissions/0fcc7371-089c-4308-bc07-b5e26052951d

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
theorem _root_.solution (σ : K →+* K) (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map σ)ᵀ = σ c • (A.map σ)ᵀ := by
  ext i j; simp
end GlobalTheory.MatSqrtNearOne
