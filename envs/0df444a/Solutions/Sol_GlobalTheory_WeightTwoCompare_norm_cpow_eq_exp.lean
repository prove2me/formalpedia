-- Prove2me | solution 1 for GlobalTheory.WeightTwoCompare.norm_cpow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:33.83862+00:00
-- url     : https://prove2.me/submissions/ca9a5ab3-d0c0-434d-a8fd-d4bc4d461618

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumDeformedLatticeEisensteinSummandWeightTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.WeightTwoCompare
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.WeightTwoCompare
theorem _root_.solution {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring
end GlobalTheory.WeightTwoCompare
