-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_sixth_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:31.267205+00:00
-- url     : https://prove2.me/submissions/5ee67e9e-1b73-4d29-9a1f-a08739ff8a49

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
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
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution :
    Function.Injective (fun r : ℕ => (r : O) ^ 6) := by
  intro r s hrs
  have hcast : ((r ^ 6 : ℕ) : O) = ((s ^ 6 : ℕ) : O) := by
    simpa only [Nat.cast_pow] using hrs
  exact Nat.pow_left_injective (by decide : 6 ≠ 0) (Nat.cast_injective hcast)
end OAI.ActualEisensteinCubic
