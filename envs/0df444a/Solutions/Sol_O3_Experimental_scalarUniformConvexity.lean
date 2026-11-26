-- Prove2me | solution 1 for O3.Experimental.scalarUniformConvexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:47.321184+00:00
-- url     : https://prove2.me/submissions/2299847d-5a29-4a39-8a07-b02f716915bb

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarUniformConvexity_of_le
import Theorems.Thm_O3_Experimental_scalarJ_neg
import Theorems.Thm_O3_Experimental_scalarEnergy_neg
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
theorem _root_.solution {p x y : ℝ} (hp : 2 < p) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by
  rcases le_total x y with hxy | hyx
  · exact scalarUniformConvexity_of_le hp hxy
  · have hneg := scalarUniformConvexity_of_le hp (neg_le_neg hyx)
    rw [scalarEnergy_neg, scalarEnergy_neg, scalarJ_neg] at hneg
    simp only [neg_sub_neg, neg_mul] at hneg
    rw [abs_sub_comm] at hneg
    convert hneg using 1
    ring_nf
end O3.Experimental
