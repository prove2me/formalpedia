-- Prove2me | solution 1 for GeneralPieces.Dual.sgn_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:04:53.661143+00:00
-- url     : https://prove2.me/submissions/8868cf0a-d3b0-43cd-8e2d-ea3672e802cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem solution (μ : List ℕ+) : sgn μ * sgn μ = 1 := by
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    have h2 : ((-1 : ℤ) ^ ((n : ℕ) - 1)) * ((-1 : ℤ) ^ ((n : ℕ) - 1)) = 1 := by rw [← mul_pow]; simp
    calc sgn (n :: μ) * sgn (n :: μ) = (((-1 : ℤ) ^ ((n : ℕ) - 1)) * ((-1 : ℤ) ^ ((n : ℕ) - 1))) * (sgn μ * sgn μ) := by rw [h1]; ring
      _ = 1 := by rw [h2, ih]; norm_num
