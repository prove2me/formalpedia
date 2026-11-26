-- Prove2me | solution 1 for O3.pairing_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:56:32.835491+00:00
-- url     : https://prove2.me/submissions/d78f150e-234d-452d-8a32-59f6079f9b42

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpNorm_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpNorm_neg

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (x y : Point d) : pairing x y = pairing y x := by
  simp only [pairing, mul_comm]
end O3
