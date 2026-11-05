-- Prove2me | solution 1 for GeneralPieces.TopDisplay.top_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:42:13.79991+00:00
-- url     : https://prove2.me/submissions/b08d08de-ab88-4094-8fb1-8dc462beca2f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_kme_of_main
import Theorems.Thm_GeneralPieces_TopDisplay_top_level
import Theorems.Thm_ClauseBound_Gen_Seq_topK_idx
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ (Atop C₀ 10 : ℕ) * k * m * e ρ x₀ (Q.pick (root9 m)).1.length := by
  obtain ⟨h1, -, -, -, h5⟩ := top_level P ρ x₀ C₀ hρ hx Q hQ k m hk hm
  have hKi : (solverOf P).K (Q.idx (Q.pick (root9 m)).1.length) = K x₀ (Q.pick (root9 m)).1.length := by rw [hQ]; exact Seq.topK_idx P x₀ _
  have hK2 := Q.K_two (Q.pick (root9 m)).1.length
  have he := Q.e_ge (Q.pick (root9 m)).1.length
  rw [hKi] at hK2 he
  have e1 : (1 - 1 / 90 : ℝ) = 1 - 1 / (9 * ((10 : ℕ) : ℝ)) := by norm_num
  rw [e1] at h5
  exact kme_of_main _ C₀ k m 10 (203 * (2 * C₀ + 15)) _ _ hK2 (by norm_num) h1 he h5
end GeneralPieces.TopDisplay
