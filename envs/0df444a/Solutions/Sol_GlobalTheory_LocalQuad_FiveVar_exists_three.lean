-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.exists_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:09.474873+00:00
-- url     : https://prove2.me/submissions/580249b1-f5bc-4c1c-b3ad-7e6b403b730c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f j = f i ∧ f k = f i := by
  revert f
  decide
end GlobalTheory.LocalQuad.FiveVar
