-- Prove2me | solution 1 for GlobalTheory.JR.SLGen.eq_top_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:28.932384+00:00
-- url     : https://prove2.me/submissions/2dfd73dd-a078-46b8-b977-75979a9d1768

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Theorems.Thm_GlobalTheory_JR_SLGen_nS_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_wS_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_wS_inv_coe
import Theorems.Thm_GlobalTheory_JR_SLGen_decomp

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
theorem _root_.solution (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by
  have hl : ∀ c : F, (wS F)⁻¹ * nS (-c) * wS F ∈ H := fun c =>
    H.mul_mem (H.mul_mem (H.inv_mem hw) (hn _)) hw
  have key : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [decomp g hc]
    exact H.mul_mem (H.mul_mem (hn _) (hl _)) (hn _)
  rw [eq_top_iff]
  intro g _
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.2
    rw [Matrix.det_fin_two, hc] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h; rw [h] at hdet; simp at hdet
    set L1 : SpecialLinearGroup (Fin 2) F := (wS F)⁻¹ * nS (-(1 : F)) * wS F
    have h1 : L1 * g ∈ H := by
      apply key
      simp only [L1, Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    have : g = L1⁻¹ * (L1 * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc
end GlobalTheory.JR.SLGen
