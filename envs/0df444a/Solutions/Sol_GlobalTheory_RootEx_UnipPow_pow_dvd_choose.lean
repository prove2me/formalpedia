-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.pow_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:55.003518+00:00
-- url     : https://prove2.me/submissions/f08c9bf0-e247-47ad-9505-1007090bfee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution {q : ℕ} (hq : q.Prime) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    q ^ (m - i) ∣ (q ^ m).choose i := by
  have := Fact.mk hq
  rcases Nat.eq_zero_or_pos ((q ^ m).choose i) with h0 | hpos
  · rw [h0]
    exact dvd_zero _
  have hdvd : q ^ m ∣ (q ^ m).choose i * i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero m hq.ne_zero)
    rw [hN]
    exact ⟨N.choose j, (Nat.add_one_mul_choose_eq N j).symm⟩
  have hv : m ≤ padicValNat q ((q ^ m).choose i) + padicValNat q i := by
    rw [← padicValNat.mul hpos.ne' hi]
    exact (padicValNat_dvd_iff_le (mul_ne_zero hpos.ne' hi)).mp hdvd
  have hi' : padicValNat q i < i := (padicValNat_le_nat_log i).trans_lt (Nat.log_lt_self q hi)
  exact (padicValNat_dvd_iff_le hpos.ne').mpr (by omega)
end GlobalTheory.RootEx.UnipPow
