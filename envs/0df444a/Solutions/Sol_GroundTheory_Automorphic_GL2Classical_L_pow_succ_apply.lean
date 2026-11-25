-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.L_pow_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:31.221256+00:00
-- url     : https://prove2.me/submissions/855d4885-4e25-4335-80c3-f16b46770c81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_J_pow_apply

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
theorem _root_.solution (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) (hLR : Ll * Rr - Rr * Ll = (4 * I) • Jj)
    {κ : ℂ} {t : E} (ht : Jj t = κ • t) (hL : Ll t = 0) (j : ℕ) :
    Ll ((Rr ^ (j + 1)) t) = (4 * I * (j + 1) * (κ + I * j)) • (Rr ^ j) t := by
  have hcomm : ∀ v, Ll (Rr v) = Rr (Ll v) + (4 * I) • Jj v := by
    intro v
    have := congrArg (fun F : Module.End ℂ E => F v) hLR
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [← this]
    abel
  induction j with
  | zero =>
    rw [pow_one, hcomm, hL, map_zero, zero_add, ht, smul_smul, pow_zero, Module.End.one_apply]
    congr 1
    push_cast
    ring
  | succ j ih =>
    rw [pow_succ' Rr (j + 1), Module.End.mul_apply, hcomm, ih, map_smul, J_pow_apply hJR ht, smul_smul]
    have e : Rr ((Rr ^ j) t) = (Rr ^ (j + 1)) t := by rw [pow_succ', Module.End.mul_apply]
    rw [e, ← add_smul]
    congr 1
    push_cast
    ring
end GroundTheory.Automorphic.GL2Classical
