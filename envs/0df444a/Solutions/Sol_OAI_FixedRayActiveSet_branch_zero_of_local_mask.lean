-- Prove2me | solution 1 for OAI.FixedRayActiveSet.branch_zero_of_local_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:44.624756+00:00
-- url     : https://prove2.me/submissions/6a23380b-da8a-451b-84b3-d87e5af78604

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization

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
open OAI.FixedRayActiveSet
open scoped BigOperators
namespace OAI.FixedRayActiveSet
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (scalar dual inactive : ι → ℂ)
    (i : ι) (hi : i ∈ A) (hzero : dual i = 0) :
    (∏ k ∈ A, scalar k * dual k) *
      (∏ k ∈ I \ A, inactive k) = 0 := by
  have hprod : (∏ k ∈ A, scalar k * dual k) = 0 :=
    Finset.prod_eq_zero hi (by rw [hzero, mul_zero])
  rw [hprod, zero_mul]
end OAI.FixedRayActiveSet
