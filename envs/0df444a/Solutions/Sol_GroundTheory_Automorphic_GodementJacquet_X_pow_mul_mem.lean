-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.X_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:51.783927+00:00
-- url     : https://prove2.me/submissions/ae1a9b3d-d4ea-488a-b6ec-45440ffa0cc8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
variable {I : Submodule ℂ (RatFunc ℂ)}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (k : ℕ) {R : RatFunc ℂ} (hR : R ∈ I) :
    RatFunc.X ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X, mul_assoc]
    exact hX _ ih
end GroundTheory.Automorphic.GodementJacquet
