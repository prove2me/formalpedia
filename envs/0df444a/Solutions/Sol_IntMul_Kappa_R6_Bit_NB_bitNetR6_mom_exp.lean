-- Prove2me | solution 1 for IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-20T21:04:45.497049+00:00
-- url     : https://prove2.me/submissions/de2f8ddd-50db-4944-b16d-5ab1747af848

-- Round-six κ development (integer-multiplication-kappa): bridge for the bit-network moment statement.

import Mathlib
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_bitNetR6_mom
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul IntMul.Kappa IntMul.Kappa.R6 IntMul.Kappa.R6.Bit

/-- `bitNetR6_mom` with `BitNetR6MomStmt` unfolded (definitional). -/
theorem solution :
  ∃ (T : ℕ) (C : QHNet (ZMod 2) 148225616 T 529) (q₀ : ℕ), C.RunsOK ∧
    (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist 529 τ ≤ histMoment Jain.bitR6 529 τ :=
  IntMul.Kappa.R6.Bit.NB.bitNetR6_mom
