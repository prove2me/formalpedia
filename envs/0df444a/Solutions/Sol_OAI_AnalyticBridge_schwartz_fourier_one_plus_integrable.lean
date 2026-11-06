-- Prove2me | solution 1 for OAI.AnalyticBridge.schwartz_fourier_one_plus_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:49.881772+00:00
-- url     : https://prove2.me/submissions/8430170d-3b86-4635-8210-8328f53cab87

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.AnalyticBridge
namespace OAI.AnalyticBridge
theorem _root_.solution
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)
end OAI.AnalyticBridge
