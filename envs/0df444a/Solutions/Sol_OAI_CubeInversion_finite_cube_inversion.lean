-- Prove2me | solution 1 for OAI.CubeInversion.finite_cube_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:16:07.189771+00:00
-- url     : https://prove2.me/submissions/5c50b66f-8ae2-4f35-a1a4-9c3770c1eb73

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_CubeInversion_cube_coefficient_filter
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
open OAI.CubeInversion
namespace OAI.CubeInversion
theorem _root_.solution
    (S : Finset ℕ) (hS : 1 ∈ S) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ m ∈ S, ∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
        c 1 * W 1 := by
  simp_rw [cube_coefficient_filter (c := c) (W := W) (hc := hc)]
  simp [hS]
end OAI.CubeInversion
