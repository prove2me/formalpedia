-- Prove2me | solution 1 for O3.Experimental.scalarEnergy_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:05.93847+00:00
-- url     : https://prove2.me/submissions/d9fce423-d836-426e-ac3a-6c6c528a589c

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution (p x : ℝ) : scalarEnergy p (-x) = scalarEnergy p x := by
  simp only [scalarEnergy, abs_neg]
end O3.Experimental
