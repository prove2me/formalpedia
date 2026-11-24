-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.hTransAB_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:52.706118+00:00
-- url     : https://prove2.me/submissions/b2c8f4b8-cafd-4dfb-9d10-7d711ac90d94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_cpow_eq

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
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {a b : ℕ} {σ : ℂ} {ν y : ℝ} (hy : y ≠ 0) : hTransAB a b σ ν y = ∫ t, igE a b σ ν y t := by
  unfold hTransAB igE
  congr 1; funext t
  rw [← cpow_eq hy σ]; rfl
end GlobalTheory.HeckeTwoDY
