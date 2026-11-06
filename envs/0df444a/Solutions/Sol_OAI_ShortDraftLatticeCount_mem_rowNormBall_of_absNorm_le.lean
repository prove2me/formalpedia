-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:47.792583+00:00
-- url     : https://prove2.me/submissions/e73dfb76-b649-4236-b050-f4899aa9628e

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ShortDraftLatticeCount_mem_rowNormBall_of_qNat_le
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
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
open OAI.ShortDraftLatticeCount
open ActualEisensteinCoordinates
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution (H : ℕ) (u : O)
    (h : Ideal.absNorm (Ideal.span {u}) ≤ H) :
    u ∈ rowNormBall H := by
  apply mem_rowNormBall_of_qNat_le
  simpa only [ActualEisensteinCubic.qNat_eq_absNorm_span] using h
end OAI.ShortDraftLatticeCount
