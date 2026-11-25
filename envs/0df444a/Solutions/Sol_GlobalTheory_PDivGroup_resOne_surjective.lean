-- Prove2me | solution 1 for GlobalTheory.PDivGroup.resOne_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:28.889614+00:00
-- url     : https://prove2.me/submissions/99dc1715-cd07-478e-aa26-e6afb0ed1f81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))
end GlobalTheory.PDivGroup
