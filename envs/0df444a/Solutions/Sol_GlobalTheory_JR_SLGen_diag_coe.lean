-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.diag_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:12:23.944891+00:00
-- url     : https://prove2.me/submissions/fdceeff6-1a12-4004-8066-a091657c7347

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Theorems.Thm_GlobalTheory_JR_SLGen_nS_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_wS_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_wS_inv_coe

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
theorem _root_.solution {ϖ : F} (hϖ : ϖ ≠ 0) :
    ((nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![ϖ, 0; 0, ϖ⁻¹] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ] <;> field_simp <;> ring
end GlobalTheory.JR.SLGen
