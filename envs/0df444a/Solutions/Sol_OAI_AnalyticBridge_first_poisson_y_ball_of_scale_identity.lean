-- Prove2me | solution 1 for OAI.AnalyticBridge.first_poisson_y_ball_of_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:37.041385+00:00
-- url     : https://prove2.me/submissions/de8bb1cf-e2ca-4e6f-9574-6dcafdf7441d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_AnalyticBridge_first_poisson_local_ratio_bound
import Theorems.Thm_OAI_AnalyticBridge_first_poisson_y_ball
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
    (L B F K A1 A2 C d c E s J2 J h y Y : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hE : 0 ≤ E) (hs : 0 ≤ s) (hJ2 : 1 ≤ J2)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2) (hh : 0 ≤ h)
    (hscale : c * E * J2 ^ 2 = A1 * A2 * s)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hdenA : A1 * A2 ≠ 0 := (mul_pos hA1 hA2).ne'
  have hdenJ2 : J2 ^ 2 ≠ 0 := by positivity
  have hratioeq : c * E / (A1 * A2) = s / J2 ^ 2 := by
    apply (div_eq_div_iff hdenA hdenJ2).mpr
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hscale
  have hratio := first_poisson_local_ratio_bound c E A1 A2 s J2 J B
    hc hE hA1 hA2 hs hJ2 hB hJ hJpos hJdyad hratioeq
  exact first_poisson_y_ball L B F K A1 A2 C d c E J h y Y
    hL hB hF hK hA1 hA2 hC hd hc hE hJpos hh
    hfrequency hy hratio hY
end OAI.AnalyticBridge
