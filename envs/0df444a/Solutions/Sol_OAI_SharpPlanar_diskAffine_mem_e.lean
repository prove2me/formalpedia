-- Prove2me | solution 1 for OAI.SharpPlanar.diskAffine_mem_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:35:20.496554+00:00
-- url     : https://prove2.me/submissions/16e79a4d-1046-4079-aa93-93f22f01af70

import Mathlib
import Definitions.Def_OAIQ098E018

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma diskAffine_mem_e_oai {j : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖diskAffine j w-(diskCenter j:ℂ)‖ ≤ 1/6 := by
  simp only [diskAffine,add_sub_cancel_left,norm_div,Complex.norm_ofNat]
  linarith

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.diskAffine_mem_e_oai := @OAI.SharpPlanar.diskAffine_mem_e_oai
