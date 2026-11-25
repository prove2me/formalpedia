-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.forall_mul_map_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:41.433528+00:00
-- url     : https://prove2.me/submissions/b0455e3c-ed1c-49b4-a64b-54ea8c20d0db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_forall_mem_range_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype n] [DecidableEq n] (x : Matrix m n K) (k : GL n O) :
    (∀ i j, (x * (k : Matrix n n O).map (algebraMap O K)) i j ∈ (algebraMap O K).range) ↔
      ∀ i j, x i j ∈ (algebraMap O K).range := by
  rw [forall_mem_range_iff, forall_mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y * ((k⁻¹ : GL n O) : Matrix n n O), ?_⟩
    rw [Matrix.map_mul, hy, Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  · rintro ⟨y, rfl⟩
    exact ⟨y * (k : Matrix n n O), Matrix.map_mul⟩
end GlobalTheory.LatticeIndicator
