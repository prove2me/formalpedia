-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.conj_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:28.138362+00:00
-- url     : https://prove2.me/submissions/c4e21de1-eb00-49a7-be65-8738d153c916

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Theorems.Thm_GlobalTheory_JR_SLGen_nS_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_diag_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SLGen
variable {F : Type} [Field F]
namespace GlobalTheory.JR.SLGen
theorem _root_.solution {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, diag_coe hϖ, nS_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
end GlobalTheory.JR.SLGen
