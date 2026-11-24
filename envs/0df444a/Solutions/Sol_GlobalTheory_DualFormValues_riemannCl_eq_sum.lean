-- Prove2me | solution 1 for GlobalTheory.DualFormValues.riemannCl_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:59.708925+00:00
-- url     : https://prove2.me/submissions/d7418019-c26d-4141-813a-0512cfe6c6f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum
import Theorems.Thm_GlobalTheory_DualFormValues_trace_eq_sum
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
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormValues
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.DualFormValues
theorem _root_.solution (ξ x : E) :
    riemannCl ξ x = ∑ σ : E →+* ℂ, σ (ξ * x) • (ComplexEmbedding.conjugate σ).toRatAlgHom.toLinearMap := by
  ext y
  simp only [riemannCl, riemann, LinearMap.coe_mk, AddHom.coe_mk, trace_eq_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
end GlobalTheory.DualFormValues
