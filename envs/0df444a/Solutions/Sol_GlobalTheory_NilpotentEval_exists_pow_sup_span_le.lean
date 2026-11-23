-- Prove2me | solution 1 for GlobalTheory.NilpotentEval.exists_pow_sup_span_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:43.234196+00:00
-- url     : https://prove2.me/submissions/42e2988d-403b-457c-bc42-bed7afe9efb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open GlobalTheory.NilpotentEval
variable {A : Type*} [CommRing A]
namespace GlobalTheory.NilpotentEval
theorem _root_.solution (K : Ideal A) {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ j, ∃ M : ℕ, a j ^ M ∈ K) : ∃ N : ℕ, (K ⊔ Ideal.span (Set.range a)) ^ N ≤ K := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Ideal.span (Set.range a) ^ N ≤ K :=
    Ideal.exists_pow_le_of_le_radical_of_fg
      (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ha j))
      (Submodule.fg_span (Set.finite_range a))
  refine ⟨N, ?_⟩
  rw [← Ideal.mk_ker (I := K), ← Ideal.map_eq_bot_iff_le_ker] at hN
  conv_rhs => rw [← Ideal.mk_ker (I := K)]
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, ← Ideal.map_pow]
  exact hN
end GlobalTheory.NilpotentEval
