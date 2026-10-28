-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.good_primes_edges
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:10:42.613995+00:00
-- url     : https://prove2.me/submissions/85b3c17e-2396-4004-a181-82cebb57ff76

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimesEdges
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK)
open IntMul.Kappa.R8.Bit.Oppbank.Net0P
open IntMul.Kappa.R8.Bit.Oppbank.GoodPrimesEdges

/-- RunsOK ∧ EdgesOK_large for densified net0P. -/
theorem solution :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0P ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0P (q ^ f)) :=
  net0_runs_edges
