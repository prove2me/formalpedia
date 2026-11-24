-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.monomial_one_mem_span_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:05.697795+00:00
-- url     : https://prove2.me/submissions/72e31ab5-3b88-4971-9a25-66d68fc551a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
open MvPowerSeries
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    (monomial α (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ α.degree := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : (monomial (a + b) (1 : R) : MvPowerSeries σ R) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_add, pow_add]
    exact Ideal.mul_mem_mul ha hb
  | single s n =>
    rw [← X_pow_eq, Finsupp.degree_single]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self s)) n
end GlobalTheory.CompleteBaseChange
