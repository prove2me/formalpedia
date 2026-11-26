-- Prove2me | solution 1 for O3.Stage2RouteA.lpNorm_sq_eq_lpPower_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:25.095037+00:00
-- url     : https://prove2.me/submissions/8ee3e1f2-5a06-4d23-8545-762a0f0b408e

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ (2 : ℕ) = (lpPower p z) ^ (2 / p) := by
  unfold lpNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (lpPower_nonneg p z)]
  congr 1
  norm_num
  field_simp
end O3.Stage2RouteA
