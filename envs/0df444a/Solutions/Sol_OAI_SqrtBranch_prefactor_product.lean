-- Prove2me | solution 1 for OAI.SqrtBranch.prefactor_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:07.720135+00:00
-- url     : https://prove2.me/submissions/c045d914-291e-4094-a347-8f5aa76e25ca

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_SqrtBranch_cpow_half_product
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
open Filter Real Asymptotics
open OAI.SqrtBranch
open Complex
namespace OAI.SqrtBranch
theorem _root_.solution {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)
end OAI.SqrtBranch
