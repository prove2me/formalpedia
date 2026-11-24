-- Prove2me | solution 1 for GlobalTheory.HeckeMellinProd.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:31.856555+00:00
-- url     : https://prove2.me/submissions/61f27f87-a26f-4ae0-9fe8-da248a1556d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Theorems.Thm_GlobalTheory_HeckeMellinProd_coord

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
theorem _root_.solution (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by
  unfold GlobalTheory.HeckeMellin.term GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeTheta.dil
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact coord (n i) s (v i) (y i)
end GlobalTheory.HeckeMellinProd
