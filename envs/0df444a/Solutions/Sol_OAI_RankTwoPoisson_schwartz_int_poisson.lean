-- Prove2me | solution 1 for OAI.RankTwoPoisson.schwartz_int_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:45.533548+00:00
-- url     : https://prove2.me/submissions/e9703205-731d-467c-a192-c1c45fdee7f6

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, (𝓕 f) (n : ℝ) := by
  simpa [fourier_eval_zero] using
    SchwartzMap.tsum_eq_tsum_fourier f 0
end OAI.RankTwoPoisson
