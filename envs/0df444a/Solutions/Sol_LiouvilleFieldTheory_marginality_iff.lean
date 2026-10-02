-- Prove2me | solution 1 for LiouvilleFieldTheory.marginality_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:59:52.892821+00:00
-- url     : https://prove2.me/submissions/dc835ada-4cde-4bd8-830d-7227eed91435

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex
open LiouvilleFieldTheory

theorem solution (b Q : ℂ) (hb : b ≠ 0) :
    b * (Q - b) = 1 ↔ Q = b + b⁻¹ := by
  constructor
  · intro h
    have hqb : Q - b = b⁻¹ := by
      have h' : b⁻¹ * (b * (Q - b)) = b⁻¹ := by
        simpa using congrArg (fun z : ℂ => b⁻¹ * z) h
      calc
        Q - b = b⁻¹ * b * (Q - b) := by field_simp [hb]
        _ = b⁻¹ * (b * (Q - b)) := by ring
        _ = b⁻¹ := h'
    calc
      Q = (Q - b) + b := by ring
      _ = b⁻¹ + b := by rw [hqb]
      _ = b + b⁻¹ := by ring
  · intro h
    rw [h]
    field_simp [hb]
    ring
