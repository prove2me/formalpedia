-- Prove2me | solution 1 for HessianDamping.IPAHD.vK_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:44:13.640898+00:00
-- url     : https://prove2.me/submissions/08a5c09b-9a96-4b5d-92cb-31c9b3948849

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
import Definitions.Def_HessianDamping_IPAHD_Setting
set_option autoImplicit false
open GoldenRatioVI.Shared HessianDamping.IPAHD


theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (xstar : H) (α h : ℝ) (β b : ℕ → ℝ) (x : ℕ → H)
    (k : ℕ) (hk : 1 ≤ k)
    (h8 : (k : ℝ) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) + α • (x (k + 1) - x k)
      + (β k * h * k) • (gradient f (x (k + 1)) - gradient f (x k))
      + (b k * h ^ 2 * k) • gradient f (x (k + 1)) = 0) :
    vK f α h β x xstar (k + 1) - vK f α h β x xstar k
      = (h * (β (k + 1) + k * (β (k + 1) - β k) - b k * h * k)) • gradient f (x (k + 1)) := by
  unfold vK
  simp only [Nat.add_sub_cancel]
  push_cast
  refine sub_eq_zero.mp (Eq.trans ?_ h8)
  module
