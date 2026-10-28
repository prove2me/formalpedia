-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.oppbank_net
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:43:31.300879+00:00
-- url     : https://prove2.me/submissions/b0fa2a81-3725-495c-a65d-e0ac9e0fb425
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankFormalOK2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0Pnd_FormalOK_large
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0Pnd_mom_eq
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
open IntMul.Kappa.R8.Bit.Oppbank.FormalOK2
open IntMul.Kappa.R8.Bit.Oppbank

/-!
Sketch reduction of `oppbank_net` to:
* `FormalOK2.net0_runs_edges` (RunsOK ∧ EdgesOK — published definition)
* `net0Pnd_FormalOK_large` (Open)
* `net0Pnd_mom_eq` (Open)
-/

theorem solution :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ = histMoment bitR8 529 τ := by
  obtain ⟨qE, hRuns, hE⟩ := net0_runs_edges
  obtain ⟨qF, hF⟩ := net0Pnd_FormalOK_large
  refine ⟨3217907, net0Pnd, qE + qF, hRuns, ?_, ?_⟩
  · intro q hq hlt f
    exact ⟨hE q hq (by omega) f, hF q hq (by omega) f⟩
  · intro τ _ _
    exact net0Pnd_mom_eq τ
