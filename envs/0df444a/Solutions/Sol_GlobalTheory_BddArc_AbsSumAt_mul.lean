-- Prove2me | solution 1 for GlobalTheory.BddArc.AbsSumAt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:26:58.094593+00:00
-- url     : https://prove2.me/submissions/800f010e-c0d6-462d-b886-800af91af939

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.BddArc
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]
namespace GlobalTheory.BddArc
namespace AbsSumAt
theorem _root_.solution {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f * g) (a * b) := by
  have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring
  constructor
  · simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => PowerSeries.coeff n f * u ^ n)
      (g := fun n => PowerSeries.coeff n g * u ^ n) hf.1 hg.1
  · rw [← hf.2, ← hg.2, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1]
    simp only [e]
end AbsSumAt
end GlobalTheory.BddArc
