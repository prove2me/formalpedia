-- Prove2me | solution 1 for GlobalTheory.BK.TameGal.not_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:49.516256+00:00
-- url     : https://prove2.me/submissions/9ddcb0f1-ceb7-4c8a-81db-a86b24681f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.TameGal
variable {l}
variable [NeZero e]
namespace GlobalTheory.BK.TameGal
theorem _root_.solution : ¬ l ∣ Nat.card (TameGal K l e a) := by
  rw [card, (Fact.out : l.Prime).dvd_mul, not_or]
  refine ⟨fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ?_), TameDescentExponentData.not_dvd K e⟩
  refine (Nat.dvd_add_right h).1 ?_
  rw [TameDescentExponentData.succ_eq (K := K) (l := l) (a := a)]
  exact dvd_pow_self l (NeZero.ne a)
end GlobalTheory.BK.TameGal
