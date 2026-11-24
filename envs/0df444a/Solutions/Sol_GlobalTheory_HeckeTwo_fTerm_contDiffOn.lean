-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.fTerm_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:48.943575+00:00
-- url     : https://prove2.me/submissions/a948d15f-4d88-4261-b69f-941a5ee90f0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_contDiffOn_hTrans

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
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
    ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  intro F _ _ b ν hb σ hσ
  unfold fTerm
  refine contDiffOn_prod fun τ _ => ?_
  have he : ContDiff ℝ ∞ (fun z : Emb F → ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ τ))))).cexp
  have hg : ContDiff ℝ ∞ (fun z : Emb F → ℂ => τ b * (z τ).im) :=
    contDiff_const.mul (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ τ))
  have hh : ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => hTrans σ (τ ν) (τ b * (z τ).im)) (upperHalf F) :=
    (TermSmooth.contDiffOn_hTrans σ hσ (τ ν)).comp hg.contDiffOn
      fun z hz => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact he.contDiffOn.mul hh
end GlobalTheory.HeckeTwo
