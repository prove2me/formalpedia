-- Prove2me | solution 1 for GlobalTheory.WeightTwoSum.contDiffOn_logFac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:36.673264+00:00
-- url     : https://prove2.me/submissions/de1ddfc0-6b5e-44d2-bacb-11309b0dfd12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_homFac_ne_zero
import Theorems.Thm_GlobalTheory_WeightTwoSum_contDiff_homFac
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply

set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.WeightTwoSum
theorem _root_.solution : ContDiffOn ℝ ∞ (logFac : (I → ℂ) → ℂ) (polydisc I) := by
  have h1 : ContDiff ℝ ∞ (homFac : (I → ℂ) → ℂ) := contDiff_homFac.restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun z : I → ℂ => Complex.normSq (homFac z)) := by
    simp only [Complex.normSq_apply]
    exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp h1)).add
      ((Complex.imCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp h1))
  have h3 : ContDiffOn ℝ ∞ (fun z : I → ℂ => Real.log (Complex.normSq (homFac z))) (polydisc I) :=
    h2.contDiffOn.log fun z hz => (Complex.normSq_pos.2 (homFac_ne_zero hz)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h3
end GlobalTheory.WeightTwoSum
