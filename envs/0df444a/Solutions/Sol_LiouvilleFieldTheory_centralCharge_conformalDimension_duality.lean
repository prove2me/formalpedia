-- Prove2me | solution 1 for LiouvilleFieldTheory.centralCharge_conformalDimension_duality
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T13:12:38.940314+00:00
-- url     : https://prove2.me/submissions/493e82cc-ba7a-4586-b6d4-20e6da7dc744

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex
open LiouvilleFieldTheory

theorem solution (b α : ℂ) :
    centralCharge b⁻¹ = centralCharge b ∧
      conformalDimension b⁻¹ α = conformalDimension b α := by
  constructor
  · unfold centralCharge backgroundCharge
    calc 1 + 6 * (b⁻¹ + (b⁻¹)⁻¹) ^ 2
        = 1 + 6 * (b⁻¹ + b) ^ 2 := by simp [inv_inv]
      _ = 1 + 6 * (b + b⁻¹) ^ 2 := by ring
  · unfold conformalDimension backgroundCharge
    calc α * ((b⁻¹ + (b⁻¹)⁻¹) - α)
        = α * ((b⁻¹ + b) - α) := by simp [inv_inv]
      _ = α * ((b + b⁻¹) - α) := by ring
