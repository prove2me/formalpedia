-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.fac_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:32.509613+00:00
-- url     : https://prove2.me/submissions/7464164b-8293-461c-8777-49b3e1a4b2c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Theorems.Thm_GlobalTheory_T_gamma_integral_exp_substitution_real_line


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
theorem _root_.solution (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    Integrable (fac w r) ∧ ∫ t, fac w r t = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) :=
  GlobalTheory.T.gamma_integral_exp_substitution_real_line r hr w hw
end GlobalTheory.HeckeMellinProd
