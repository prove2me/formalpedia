-- Prove2me | solution 1 for GlobalTheory.TargetStatementSixOneSixtyEight.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:34.448862+00:00
-- url     : https://prove2.me/submissions/07c7c51c-9484-4d3f-96a6-61e06183ce20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetStatementSixOneSixtyEight
open NumberField
namespace GlobalTheory.TargetStatementSixOneSixtyEight
theorem _root_.solution {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, h1⟩ := h1
    obtain ⟨c2, hc2, h2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add, mul_comm c1 c2, mul_smul, mul_comm c2 c1, mul_smul]
    exact L.add_mem (L.smul_mem c2 h1) (L.smul_mem c1 h2)
  | smul a x _ h =>
    obtain ⟨c0, hc0, h0⟩ := h
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨c0 * (s : RingOfIntegers E), mul_ne_zero hc0 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have key : (s : RingOfIntegers E) • (a • x) = b • x := by
      rw [← algebraMap_smul E (s : RingOfIntegers E), smul_smul, mul_comm, hs, algebraMap_smul]
    rw [mul_smul, key, smul_comm c0 b x]
    exact L.smul_mem b h0
end GlobalTheory.TargetStatementSixOneSixtyEight
