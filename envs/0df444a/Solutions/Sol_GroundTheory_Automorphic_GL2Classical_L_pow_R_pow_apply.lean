-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.L_pow_R_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:14.535179+00:00
-- url     : https://prove2.me/submissions/c9969dcf-c621-4f58-a6ba-48cb3425f9e0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_L_pow_succ_apply

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
    (Ll ^ j) ((Rr ^ j) t) = (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (κ + I * m))) • t := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ Ll j, Module.End.mul_apply, L_pow_succ_apply hJR hLR ht hL, map_smul, ih, smul_smul,
      Finset.prod_range_succ, mul_comm]
end GroundTheory.Automorphic.GL2Classical
