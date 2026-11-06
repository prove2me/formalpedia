-- Prove2me | solution 1 for OAI.EisensteinAbelFiber.scaled_shifted_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:52:10.088757+00:00
-- url     : https://prove2.me/submissions/46e73005-7519-40dc-9507-98df74143ca3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_EisensteinAbelFiber_shifted_gaussian_mass
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
open OAI.EisensteinAbelFiber
open scoped Topology
open Filter
namespace OAI.EisensteinAbelFiber
theorem _root_.solution (q : ℝ) (hq : 0 < q)
    (x y : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted (η*q) x y z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 * q) : ℝ) : ℂ))) := by
  have hscale : Tendsto (fun η : ℝ => η*q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun η : ℝ => η)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using hid.mul_const q
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hη hq
  have hlim := (shifted_gaussian_mass x y).comp hscale
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hlim' := hlim.const_mul (1 / (q : ℂ))
  convert hlim' using 1
  · funext η
    dsimp
    push_cast
    field_simp [hqC]
  · push_cast
    field_simp [hqC]
end OAI.EisensteinAbelFiber
