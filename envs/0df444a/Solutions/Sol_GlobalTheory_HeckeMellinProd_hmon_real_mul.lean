-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.hmon_real_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:44.035482+00:00
-- url     : https://prove2.me/submissions/e9aed415-bdb9-4b23-8b50-8aca15b4da4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma

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
theorem _root_.solution (n : ℤ) (c : ℝ) (z : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((c : ℂ) * z) = (c : ℂ) ^ n.natAbs * GlobalTheory.HeckeTheta.hmon n z := by
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · rw [map_mul, Complex.conj_ofReal, mul_pow]; congr 2; omega
  · rw [mul_pow]; congr 2; omega
end GlobalTheory.HeckeMellinProd
