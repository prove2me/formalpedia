-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.completed_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:47:22.661194+00:00
-- url     : https://prove2.me/submissions/a4381295-ae44-4695-9fc9-828628210e85

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_norm_periodicCoeff_le
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_theta_sub_zero_hasSum
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_hasMellin
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_nonneg
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_weighted_normForm


set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by
  have hsum : Summable (fun n : ℤ × ℤ => ‖periodicCoeff w n‖ /
      normForm n.1 n.2 ^ s.re) :=
    summable_weighted_normForm (norm_periodicCoeff_le w) hs
  have h := hasSum_mellin_pi_mul₀
    (a := periodicCoeff w) (p := fun n : ℤ × ℤ => normForm n.1 n.2)
    (F := fun t => (pair w).f t - (pair w).f₀)
    (fun _ => normForm_nonneg _ _) (by linarith : 0 < s.re)
    (fun _ ht => theta_sub_zero_hasSum w ht) hsum
  rwa [(pair_hasMellin w hs).2] at h
end OAI.SevenEighths.HeckeTheta
