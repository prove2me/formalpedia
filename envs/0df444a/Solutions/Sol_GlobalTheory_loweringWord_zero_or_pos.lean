-- Prove2me | solution 1 for GlobalTheory.loweringWord_zero_or_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:06.995711+00:00
-- url     : https://prove2.me/submissions/0dac3085-db9c-4f0b-bac7-3bac65fc321f

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsStableSubmoduleTopWeightLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}
namespace GlobalTheory
theorem _root_.solution {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega
end GlobalTheory
