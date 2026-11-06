-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.mem_rowNormBall_of_qNat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:21.090537+00:00
-- url     : https://prove2.me/submissions/1a6e9a86-3c34-41da-be25-f2648dff6bce

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ShortDraftLatticeCount_coordinate_squares
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg


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
    (h : qNat u ≤ H) : u ∈ rowNormBall H := by
  classical
  have hq : q (coords u) ≤ (H : ℤ) := by
    change (q (coords u)).toNat ≤ H at h
    have hnonneg := qO_nonneg u
    omega
  let a := (coords u).1
  let b := (coords u).2
  have hab : a ^ 2 - a * b + b ^ 2 ≤ (H : ℤ) := hq
  obtain ⟨ha2, hb2⟩ := coordinate_squares a b (H : ℤ)
    (by positivity) hab
  have hH : (0 : ℤ) ≤ H := by positivity
  have haL : -((H : ℤ) + 1) ≤ a := by nlinarith [sq_nonneg (H : ℤ)]
  have haU : a ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  have hbL : -((H : ℤ) + 1) ≤ b := by nlinarith [sq_nonneg (H : ℤ)]
  have hbU : b ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  unfold rowNormBall
  apply Finset.mem_image.mpr
  refine ⟨coords u, ?_, eval_coords u⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨haL, haU⟩,
     Finset.mem_Icc.mpr ⟨hbL, hbU⟩⟩
end OAI.ShortDraftLatticeCount
