-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_qNat_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:08.241901+00:00
-- url     : https://prove2.me/submissions/f34d2f32-a897-4cc0-bb36-af22859719c1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_mul
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
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (r k : ℕ) (hr : r ≠ 0) :
    qNat ((r : O) ^ k) = (r ^ 2) ^ k := by
  induction k with
  | zero =>
      simpa using rational_qNat 1 (by decide)
  | succ k ih =>
      calc
        qNat ((r : O) ^ (k + 1)) =
            qNat ((r : O) ^ k) * qNat (r : O) := by
          rw [pow_succ, qNat_mul]
        _ = (r ^ 2) ^ k * (r ^ 2) := by rw [ih, rational_qNat r hr]
        _ = (r ^ 2) ^ (k + 1) := (pow_succ (r ^ 2) k).symm
end OAI.ActualEisensteinCubic
