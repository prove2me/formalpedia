-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.ofReal_norm_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:34:53.384322+00:00
-- url     : https://prove2.me/submissions/1d1d8964-9e1e-4a6e-9a40-9f5f9a23d938

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Theorems.Thm_GlobalTheory_HeckeMellinProd_norm_fac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeMellinProd
namespace GlobalTheory.HeckeMellinProd
theorem _root_.solution (w : ℂ) (r : ℝ) (t : ℝ) :
    ((‖fac w r t‖ : ℝ) : ℂ) = fac (w.re : ℂ) r t := by
  rw [norm_fac, fac]; push_cast; rfl
end GlobalTheory.HeckeMellinProd
