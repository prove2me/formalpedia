-- Prove2me | solution 1 for GlobalTheory.TopForm.IsFreeGen.smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:14.739076+00:00
-- url     : https://prove2.me/submissions/20744d63-8535-4834-a8b5-b89c95e6da40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_unit_smul
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}
namespace GlobalTheory.TopForm
namespace IsFreeGen
theorem _root_.solution (h : IsFreeGen A ω) {a : A} : IsFreeGen A (a • ω) ↔ IsUnit a := by
  refine ⟨fun h' => ?_, fun ⟨u, hu⟩ => hu ▸ h.unit_smul u⟩
  obtain ⟨b, hb⟩ := h'.2 ω
  refine IsUnit.of_mul_eq_one b (h.1 ?_)
  simpa only [mul_comm a b, mul_smul, one_smul] using hb
end IsFreeGen
end GlobalTheory.TopForm
