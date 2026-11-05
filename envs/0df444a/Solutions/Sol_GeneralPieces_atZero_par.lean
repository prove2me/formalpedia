-- Prove2me | solution 1 for GeneralPieces.atZero_par
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:22:49.948295+00:00
-- url     : https://prove2.me/submissions/25107b40-f884-4963-b8c1-9dfa2eb7c4de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Trim_Cert
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg
import Theorems.Thm_GeneralPieces_atZero_spec
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}
namespace GeneralPieces
theorem _root_.solution (h : IsPieces ρ c P A val) {m c' : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hc : c ≤ c') (hmc : m ≤ c') : Par (atZero P c m) ρ c' where
  spec hh lam hl := atZero_spec h hm hcap hh hl
  caps hh lam hl := by
    have h0 : (0 : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := by
      have := h.rho_ge
      have h4 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
      have h5 := mul_nonneg (Nat.cast_nonneg (α := ℝ) c) (logb_nonneg hl)
      nlinarith
    have h1 : capSum (atZero P c m) hh lam ≤ ⌊4 * ρ * lam + c * Real.logb 2 (2 * lam)⌋₊ :=
      Finset.sup_le fun i hi => Nat.le_floor (h.caps lam hl i (Finset.mem_range.1 hi))
    have h2 : (capSum (atZero P c m) hh lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (by exact_mod_cast h1) (Nat.floor_le h0)
    have h3 : (c : ℝ) ≤ c' := by exact_mod_cast hc
    have h4 := mul_le_mul_of_nonneg_right h3 (logb_nonneg hl)
    linarith
  cnt hh lam hl := (h.card lam hl).trans (Nat.pow_le_pow_right (by omega) hc)
  bits hh lam hl := Nat.pow_le_pow_right (by omega) hc
  d hh lam hl := (h.size_d lam hl).trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) hc))
  need hh lam hl := Nat.mul_le_mul_right _ hc
  m_le := hmc
end GeneralPieces
