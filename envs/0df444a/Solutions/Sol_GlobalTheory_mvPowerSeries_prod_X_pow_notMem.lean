-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_prod_X_pow_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:50.667843+00:00
-- url     : https://prove2.me/submissions/735032f2-1d74-48e2-a02e-2a8536f1f7bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPowerSeries Finsupp
namespace GlobalTheory
theorem _root_.solution {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc
  rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
end GlobalTheory
