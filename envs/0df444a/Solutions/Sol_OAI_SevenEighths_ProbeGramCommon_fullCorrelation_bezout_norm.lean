-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:40.676211+00:00
-- url     : https://prove2.me/submissions/60b2737e-bcae-4e7d-b032-3d3a4a323e55

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullCorrelation_bezout
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_solutionEquiv_val
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk
attribute [local simp] OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val



set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]
namespace OAI.SevenEighths.ProbeGramCommon
theorem _root_.solution [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp
end OAI.SevenEighths.ProbeGramCommon
