-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.add_one_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:52.574438+00:00
-- url     : https://prove2.me/submissions/3015e132-4430-4a3c-b8cf-9b3d69ebb4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution {R : Type} [Ring R] {a : R} {d : ℕ} (ha : a ^ d = 0) (M : ℕ) :
    (a + 1) ^ M = ∑ i ∈ Finset.range d, (M.choose i) • a ^ i := by
  rw [(Commute.one_right a).add_pow]
  simp only [one_pow, mul_one]
  have key : ∀ s : Finset ℕ, ∑ i ∈ s, a ^ i * (M.choose i : R) = ∑ i ∈ s, M.choose i • a ^ i :=
    fun s => Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]; exact (Nat.cast_comm _ _).symm
  rw [key]
  calc ∑ i ∈ Finset.range (M + 1), M.choose i • a ^ i
      = ∑ i ∈ Finset.range (M + 1 + d), M.choose i • a ^ i := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_
        rw [Finset.mem_range] at hi'
        rw [Nat.choose_eq_zero_of_lt (by omega : M < i), zero_smul]
    _ = ∑ i ∈ Finset.range d, M.choose i • a ^ i := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        rw [pow_eq_zero_of_le (by omega : d ≤ i) ha, smul_zero]
end GlobalTheory.RootEx.UnipPow
