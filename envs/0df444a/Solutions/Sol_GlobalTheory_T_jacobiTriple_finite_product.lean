-- Prove2me | solution 1 for GlobalTheory.T.jacobiTriple_finite_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:49:55.220942+00:00
-- url     : https://prove2.me/submissions/8af93d9d-d63f-4615-9b18-1241e901a853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProductStatement
import Theorems.Thm_GlobalTheory_JacobiTriple_finTriple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (s x : ℂ), s ≠ 0 → ‖s‖ < 1 → x ≠ 0 → ∀ n : ℕ, ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  first | exact @GlobalTheory.JacobiTriple.finTriple | exact GlobalTheory.JacobiTriple.finTriple | (intros; apply GlobalTheory.JacobiTriple.finTriple <;> assumption)
end _root_.GlobalTheory.T
