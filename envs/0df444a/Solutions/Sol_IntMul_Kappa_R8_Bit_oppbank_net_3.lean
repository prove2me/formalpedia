-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.oppbank_net
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:59:22.292793+00:00
-- url     : https://prove2.me/submissions/f2658a93-7c5e-48bf-8106-9fcbc20226b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunFormalOK
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_edges
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_FormalOK_large
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_mom_eq
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK
open IntMul.Kappa.R8.Bit.Oppbank

/-!
Sketch reduction of `oppbank_net` to one-run carrier:
* `OneRunFormalOK` RunsOK + `good_edges` EdgesOK
* `net0O_FormalOK_large` (Open)
* `net0O_mom_eq` (Open)
-/

theorem net0O_runs_edges :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0O ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0O (q ^ f)) := by
  obtain ⟨q₀, h⟩ := good_edges E0 E0_Q
  exact ⟨q₀, net0O_RunsOK, fun q hq hlt f => EdgesOK_of_good_primes q₀ h hq hlt f⟩

theorem solution :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ = histMoment bitR8 529 τ := by
  obtain ⟨qE, hRuns, hE⟩ := net0O_runs_edges
  obtain ⟨qF, hF⟩ := net0O_FormalOK_large
  refine ⟨3217907, net0O, qE + qF, hRuns, ?_, ?_⟩
  · intro q hq hlt f
    exact ⟨hE q hq (by omega) f, hF q hq (by omega) f⟩
  · intro τ _ _
    exact net0O_mom_eq τ
