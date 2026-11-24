-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.integrable_prod_qCoef_mul_fsDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:28.206119+00:00
-- url     : https://prove2.me/submissions/2d256d08-f51c-4073-9afe-2f0064572b37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Theorems.Thm_GlobalTheory_FibLine_Intg_integrable_fsDens
import Theorems.Thm_GlobalTheory_FibLine_Intg_continuous_qCoef
import Theorems.Thm_GlobalTheory_FibLine_Intg_norm_qCoef_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.Intg
namespace GlobalTheory.FibLine.Intg
theorem _root_.solution (k : ℕ) (f : Fin k → Fin 2 × Fin 2) :
    Integrable (fun x : ℂ => (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) := by
  have h : Integrable (fun x : ℂ => (fsDens x : ℂ)) := integrable_fsDens.ofReal
  refine h.bdd_mul (c := 1) (continuous_finset_prod _ fun i _ => continuous_qCoef (f i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_qCoef_le x (f i)
end GlobalTheory.FibLine.Intg
