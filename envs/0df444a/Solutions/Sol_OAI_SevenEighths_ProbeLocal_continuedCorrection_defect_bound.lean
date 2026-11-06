-- Prove2me | solution 1 for OAI.SevenEighths.ProbeLocal.continuedCorrection_defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:18.896853+00:00
-- url     : https://prove2.me/submissions/cda5fb42-7110-4cd2-8825-4680a118326f

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Local
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Theorems.Thm_OAI_SevenEighths_ProbeLocal_one_sub_ne_zero_of_norm_le_half
import Theorems.Thm_OAI_SevenEighths_ProbeLocal_inv_one_sub_norm_le_two
import Theorems.Thm_OAI_SevenEighths_ProbeLocal_continuedCorrection_defect


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeLocal
namespace OAI.SevenEighths.ProbeLocal
theorem _root_.solution (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring
end OAI.SevenEighths.ProbeLocal
