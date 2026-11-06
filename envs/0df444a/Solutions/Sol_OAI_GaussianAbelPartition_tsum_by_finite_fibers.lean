-- Prove2me | solution 1 for OAI.GaussianAbelPartition.tsum_by_finite_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:34.191574+00:00
-- url     : https://prove2.me/submissions/f2542dc3-a5f6-4958-85fe-4d3456838187

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
open OAI.GaussianAbelPartition
namespace OAI.GaussianAbelPartition
theorem _root_.solution {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm
end OAI.GaussianAbelPartition
