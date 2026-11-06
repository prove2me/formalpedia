-- Prove2me | solution 1 for OAI.AnalyticBridge.first_poisson_y_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:11:05.449201+00:00
-- url     : https://prove2.me/submissions/18b6d304-2a62-4377-870d-cecd4b4a864b

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
    (L B F K A1 A2 C d c E J h y Y : ℝ)
    (_hL : 0 ≤ L) (_hB : 0 ≤ B) (_hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (_hc : 0 ≤ c)
    (hE : 0 ≤ E) (hJ : 0 < J) (_hh : 0 ≤ h)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hratio : c * E / (A1 * A2) ≤ B ^ 4 / J)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hfactor : 0 ≤ F ^ 2 * E := by positivity
  calc
    y ≤ h * F ^ 2 * E := hy
    _ ≤ (L ^ 2 * c * d / (K * A1 * A2 * C ^ 2)) * F ^ 2 * E :=
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfrequency hfactor
    _ = (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (c * E / (A1 * A2)) := by
      field_simp
    _ ≤ (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (B ^ 4 / J) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = Y := by rw [hY]; field_simp
end OAI.AnalyticBridge
