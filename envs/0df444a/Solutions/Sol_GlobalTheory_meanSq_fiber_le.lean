-- Prove2me | solution 1 for GlobalTheory.meanSq_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:06.041903+00:00
-- url     : https://prove2.me/submissions/65fd3383-aef4-4dc7-b3dc-7b6d4d7b5092

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart
import Theorems.Thm_GlobalTheory_meanSq_cn_nonneg
import Theorems.Thm_GlobalTheory_meanSq_cn_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (if n.minFac = p then cn x n else 0) ≤ sP x p := by
  classical
  unfold sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  rw [← Finset.sum_image (s := (Icc 1 N).filter (fun i => p ^ i ≤ N)) (g := fun i => p ^ i)
    (f := fun n => cn x n) (fun a _ b _ h => Nat.pow_right_injective hp.two_le h)]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter_of_ne (p := fun n => IsPrimePow n)
    (fun n _ h => by by_contra h'; exact h (meanSq_cn_eq_zero x h'))]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => meanSq_cn_nonneg hx n)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
  obtain ⟨p', i, hp', hi, rfl⟩ := (isPrimePow_nat_iff _).1 h4
  rw [hp'.pow_minFac hi.ne'] at h3
  subst h3
  refine Finset.mem_image.2 ⟨i, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hi, (Nat.lt_pow_self hp.one_lt).le.trans h2⟩, h2⟩
end GlobalTheory
