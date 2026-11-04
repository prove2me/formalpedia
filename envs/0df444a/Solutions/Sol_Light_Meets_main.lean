-- Prove2me | solution 1 for Light.Meets.main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:58.214794+00:00
-- url     : https://prove2.me/submissions/66758cb8-5385-49cd-a1e4-89c1f25c1ea7

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_Ends_callTo


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
namespace Meets
theorem _root_.solution {lim : Limits} {P : Program} {p : ℕ} {i j : ℤ} {μ : ℕ → ℤ} {T : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop} {B : ℝ} (h : Meets lim P p 1 [i, j] μ T R) (hd : 0 < lim.depth)
    (hB : ((T + 4 : ℕ) : ℝ) ≤ B) :
    ∃ (σ' : State) (c : ℕ), Exec lim P 0 (mainStmt p) ⟨frame [0, i, j], μ⟩ σ' c ∧ (c : ℝ) ≤ B ∧
      R (σ'.loc 0) σ'.mem := by
  obtain ⟨σ', c, hex, hc, hR⟩ : Ends lim P 0 (mainStmt p) ⟨frame [0, i, j], μ⟩ (T + 4)
      fun σ' => R (σ'.loc 0) σ'.mem :=
    Ends.callTo h fun _ _ hR => hR
  exact ⟨σ', c, hex, le_trans (by exact_mod_cast hc) hB, hR⟩
end Meets
end Light
