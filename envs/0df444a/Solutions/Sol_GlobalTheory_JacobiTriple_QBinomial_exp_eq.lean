-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.QBinomial.exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:36:02.384799+00:00
-- url     : https://prove2.me/submissions/23894264-e3ec-48d7-bbcf-24703bc1d703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFinite

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
open GlobalTheory GlobalTheory.JacobiTriple GlobalTheory.JacobiTriple.QBinomial
open GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple.QBinomial
theorem _root_.solution (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  rw [show k + 1 + j - k = j + 1 by omega]
  rcases k with _ | k
  · ring
  · simp only [Nat.add_sub_cancel]; ring
end GlobalTheory.JacobiTriple.QBinomial
