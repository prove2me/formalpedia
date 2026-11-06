-- Prove2me | solution 1 for OAI.AnalyticBridge.first_poisson_local_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:11:35.315752+00:00
-- url     : https://prove2.me/submissions/7baa1253-5f2a-4eb5-b24a-61900c9203ea

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization

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
    (c E A1 A2 s J2 J B : ℝ)
    (_hc : 0 ≤ c) (_hE : 0 ≤ E)
    (_hA1 : 0 < A1) (_hA2 : 0 < A2)
    (hs : 0 ≤ s) (hJ2 : 1 ≤ J2) (_hB : 0 ≤ B)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2)
    (hlocal : c * E / (A1 * A2) = s / J2 ^ 2) :
    c * E / (A1 * A2) ≤ B ^ 4 / J := by
  have hJ2sq : 1 ≤ J2 ^ 2 := by nlinarith
  have hsJ : s ≤ J := by rw [hJ]; nlinarith
  have hratio : s / J2 ^ 2 ≤ s :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hJself : J ≤ B ^ 4 / J :=
    (le_div_iff₀ hJpos).mpr (by nlinarith [sq_nonneg (B ^ 2 - J)])
  rw [hlocal]
  exact hratio.trans (hsJ.trans hJself)
end OAI.AnalyticBridge
