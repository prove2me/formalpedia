-- Prove2me | solution 1 for GlobalTheory.perfectRing_valuationSubring_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:19.874536+00:00
-- url     : https://prove2.me/submissions/508afd3a-3310-4521-a159-a37ef4888321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDomaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] {L : Type} [Field L]
    [IsAlgClosed L] (V : ValuationSubring L) [CharP V l] : PerfectRing V l := by
  haveI : ExpChar V l := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective V l ?_
  intro v
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v : L) (Nat.pos_of_ne_zero hl0)
  have hyV : y ∈ V := by
    rw [← V.valuation_le_one_iff]
    have hv : V.valuation (v : L) ≤ 1 := (V.valuation_le_one_iff _).2 v.2
    rw [← hy, map_pow] at hv
    exact (pow_le_one_iff_of_nonneg (zero_le') hl0).1 hv
  refine ⟨⟨y, hyV⟩, ?_⟩
  apply Subtype.ext
  simp [frobenius_def, hy]
end GlobalTheory
