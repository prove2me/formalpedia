-- Prove2me | solution 1 for GeneralPieces.Dual.op_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:17:39.732881+00:00
-- url     : https://prove2.me/submissions/4ea2a4b5-c938-43af-84cc-a19586aa449c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_opFacts


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℚ) (g : ι → V) (r : ℤ) (f : V) :
    op (∑ x ∈ s, c x • g x) r f = ∑ x ∈ s, c x • op (g x) r f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [op]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, opFacts.add_left, opFacts.smul_left, ih]
end GeneralPieces.Dual
