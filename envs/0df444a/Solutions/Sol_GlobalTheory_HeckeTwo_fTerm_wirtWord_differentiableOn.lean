-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:11.286301+00:00
-- url     : https://prove2.me/submissions/22877a92-d74e-4bc6-b64c-2938c7317571

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtYStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiTransformHasDerivAtHoloStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeFourierTermWirtingerWordDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_TermHol_wirtWord_eq_sum
import Theorems.Thm_GlobalTheory_T_heckeHankelTransformAB_differentiableOn_sigma
import Theorems.Thm_GlobalTheory_T_heckeHankelTransformAB_hasDerivAt_y
import Theorems.Thm_GlobalTheory_T_iteratedDeriv_heckePhiTransform_hasDerivAt_holo


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
open GlobalTheory.HeckeTwo.TermHol
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by
  intro F _ _ b ν hb w z hz
  have hJ := GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma
  obtain ⟨ι, _, c, qf, h⟩ := wirtWord_eq_sum F b ν hb hJ w
  refine DifferentiableOn.congr ?_ (fun σ hσ => h σ hσ z hz)
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.const_mul ?_ _
  unfold termQ
  refine DifferentiableOn.fun_finset_prod fun τ _ => DifferentiableOn.const_mul ?_ _
  have hy : (τ b : ℝ) * (z τ).im ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact (hJ (τ ν) (qf i τ) _ hy).2
end GlobalTheory.HeckeTwo
