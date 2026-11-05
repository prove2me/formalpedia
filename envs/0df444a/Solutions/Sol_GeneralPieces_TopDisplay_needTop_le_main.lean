-- Prove2me | solution 1 for GeneralPieces.TopDisplay.needTop_le_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:32.413121+00:00
-- url     : https://prove2.me/submissions/bcd29a6f-b176-450c-9ef7-4dbf967826ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_display
import Theorems.Thm_GeneralPieces_TopDisplay_terms_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ 90)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have h := needTop_le_display S i e C₀ k m he0 he1 hK hk hm hrate
  obtain ⟨t1, t2, t3⟩ := terms_le (S.K i) k m hK hk hm hm'
  have hA : (0 : ℝ) ≤ ((2 * C₀ + 15 : ℕ) : ℝ) := by positivity
  have h2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hA
  have h3 : ((203 * (2 * C₀ + 15) : ℕ) : ℝ) = 203 * ((2 * C₀ + 15 : ℕ) : ℝ) := by push_cast; ring
  rw [h3]
  linarith
end GeneralPieces.TopDisplay
