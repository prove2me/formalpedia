-- Prove2me | solution 1 for GlobalTheory.canonicalSigma_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:11.850296+00:00
-- url     : https://prove2.me/submissions/fcd76fe7-e34f-43aa-bbeb-b99dda18a9e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_quasiPeriod_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    canonicalSigma L (z + w) = sigmaSign L w *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * canonicalSigma L z := by
  rw [canonicalSigma, canonicalSigma, weierstrassSigma_add L hw]
  have : cexp (quasiPeriod L w * (z + w / 2)) * cexp (-(sTwo L * (z + w) ^ 2 / 2)) =
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * cexp (-(sTwo L * z ^ 2 / 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination quasiPeriod_mul_eq L z w + quasiPeriod_mul_eq L w w / 2
  linear_combination sigmaSign L w * weierstrassSigma L z * this
end GlobalTheory
