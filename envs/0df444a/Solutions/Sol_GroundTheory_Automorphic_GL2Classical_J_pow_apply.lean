-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.J_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:37.47262+00:00
-- url     : https://prove2.me/submissions/b78eea53-616c-4e1d-a37d-d06630d40921

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GL2Classical
variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) {κ : ℂ} {t : E} (ht : Jj t = κ • t) (j : ℕ) :
    Jj ((Rr ^ j) t) = (κ + 2 * I * j) • (Rr ^ j) t := by
  induction j with
  | zero => simpa using ht
  | succ j ih =>
    have h1 : Jj (Rr ((Rr ^ j) t)) = Rr (Jj ((Rr ^ j) t)) + (2 * I) • Rr ((Rr ^ j) t) := by
      have := congrArg (fun F : Module.End ℂ E => F ((Rr ^ j) t)) hJR
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [← this]
      abel
    rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
end GroundTheory.Automorphic.GL2Classical
