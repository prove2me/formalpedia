-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.X_inv_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:51.033015+00:00
-- url     : https://prove2.me/submissions/13c14c17-3257-43f1-80c0-ddc4a82a711a

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
theorem _root_.solution (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) (k : ℕ) {R : RatFunc ℂ}
    (hR : R ∈ I) : RatFunc.X⁻¹ ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X⁻¹, mul_assoc]
    exact hXinv _ ih
end GroundTheory.Automorphic.GodementJacquet
