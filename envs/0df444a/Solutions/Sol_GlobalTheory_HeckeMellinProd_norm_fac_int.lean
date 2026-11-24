-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.norm_fac_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:03.462025+00:00
-- url     : https://prove2.me/submissions/a69f1b79-69ed-4749-8cef-98c3723f1e65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Theorems.Thm_GlobalTheory_HeckeMellinProd_ofReal_norm_fac
import Theorems.Thm_GlobalTheory_HeckeMellinProd_fac_int
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeMellinProd
namespace GlobalTheory.HeckeMellinProd
theorem _root_.solution (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    ∫ t, ‖fac w r t‖ = Real.Gamma w.re * (2 * Real.pi * r) ^ (-w.re) := by
  have h := (fac_int (w.re : ℂ) (by simpa using hw) r hr).2
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_fac]
  rw [h, Complex.ofReal_mul (Real.Gamma w.re), Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast; ring_nf
end GlobalTheory.HeckeMellinProd
