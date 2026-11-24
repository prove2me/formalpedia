-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.opFst_add_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:51:55.642106+00:00
-- url     : https://prove2.me/submissions/5d68f42e-cd7b-42f5-b0b7-9c26ff0dc610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirst
import Theorems.Thm_GlobalTheory_SchwartzFstOp_sliceCLM_add_eq
import Theorems.Thm_GlobalTheory_SchwartzFstOp_opFst_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
noncomputable section
open Filter Topology Asymptotics
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by
  rw [opFst_apply, sliceCLM_add_eq]
  conv_lhs => rw [show SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f
      = (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f) + f + lineSnd v f by abel]
  simp only [map_add, SchwartzMap.add_apply]
end GlobalTheory.SchwartzFstOp
