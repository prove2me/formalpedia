-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.integrable_igE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:55.612862+00:00
-- url     : https://prove2.me/submissions/ea1a0327-d303-436c-91f9-a55805f83a9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_igE
import Theorems.Thm_GlobalTheory_HeckeTwoDY_integrable_bd
import Theorems.Thm_GlobalTheory_HeckeTwoDY_continuous_igE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {a b : ℕ} {σ : ℂ} (ν : ℝ) {y : ℝ} (hab : 2 ≤ a + b) (hσ : -1 / 2 < σ.re) (hy : y ≠ 0) :
    Integrable (fun t => igE a b σ ν y t) := by
  have hab' : (2 : ℝ) ≤ a + b := by exact_mod_cast hab
  exact (integrable_bd (k := (a : ℝ) + b + 2 * σ.re) (by linarith) hy).mono'
    (continuous_igE a b σ ν hy).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (norm_igE hy t).le)
end GlobalTheory.HeckeTwoDY
