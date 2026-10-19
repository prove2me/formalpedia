-- Prove2me | solution 1 for GoodmanWitten.eq4_quark_model_matrix_elements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:58.834345+00:00
-- url     : https://prove2.me/submissions/64a210ba-5d0b-41af-94d3-1022bf8e107f

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution (gA uP dP uN dN SP SN : ℝ)
    (hP_isovector : uP - dP = 2 * gA * SP) (hP_isosinglet : uP + dP = 2 * SP)
    (hN_isovector : dN - uN = 2 * gA * SN) (hN_isosinglet : uN + dN = 2 * SN) :
    uP = (1 + gA) * SP ∧ dP = (1 - gA) * SP ∧
      uN = (1 - gA) * SN ∧ dN = (1 + gA) * SN := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
