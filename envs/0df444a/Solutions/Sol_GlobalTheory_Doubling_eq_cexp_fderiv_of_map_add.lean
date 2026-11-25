-- Prove2me | solution 1 for GlobalTheory.Doubling.eq_cexp_fderiv_of_map_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:48.884102+00:00
-- url     : https://prove2.me/submissions/8333c34d-9ab7-4e6e-8ce9-c08040a32f6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqExpFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsBigOPowIffIteratedFDerivEqZero
import Theorems.Thm_GlobalTheory_ExpOfFrechetDerivative_eq_exp_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate
open GlobalTheory GlobalTheory.Doubling
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.Doubling
theorem _root_.solution {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)
end GlobalTheory.Doubling
