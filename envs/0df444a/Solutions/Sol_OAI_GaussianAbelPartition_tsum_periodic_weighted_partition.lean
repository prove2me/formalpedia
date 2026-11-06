-- Prove2me | solution 1 for OAI.GaussianAbelPartition.tsum_periodic_weighted_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:33.616188+00:00
-- url     : https://prove2.me/submissions/575234da-92c4-47c6-b2c8-50281cc0e282

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_GaussianAbelPartition_tsum_by_finite_fibers
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
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left
end OAI.GaussianAbelPartition
