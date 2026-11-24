-- Prove2me | solution 1 for GlobalTheory.JR.GLift.emb_preimage_glO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:55.769012+00:00
-- url     : https://prove2.me/submissions/22de5cc1-1067-4369-b4ab-f9cdd858c1ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
import Theorems.Thm_GlobalTheory_JR_GLift_embHom_apply_cc
import Theorems.Thm_GlobalTheory_JR_GLift_embHom_apply_cl
import Theorems.Thm_GlobalTheory_JR_GLift_embHom_apply_lc
import Theorems.Thm_GlobalTheory_JR_GLift_embHom_apply_ll
import Theorems.Thm_GlobalTheory_JR_GLift_coe_emb
import Theorems.Thm_GlobalTheory_JR_GLift_coe_emb_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j
end GlobalTheory.JR.GLift
