-- Prove2me | solution 1 for GlobalTheory.JR.Step.ActEmbLift.act_emb_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:46.660648+00:00
-- url     : https://prove2.me/submissions/842e1c75-fa0f-4bdb-8783-6e50454905d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrix
import Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_embHom_mul_full_mul
import Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_embHom_mulVec_eL
import Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_eL_vecMul_embHom

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.ActEmbLift
namespace GlobalTheory.JR.Step.ActEmbLift
theorem _root_.solution (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _
end GlobalTheory.JR.Step.ActEmbLift
