-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslateUnif.seminorm_lineDerivOp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:46.939586+00:00
-- url     : https://prove2.me/submissions/e7581b62-05d4-49b9-aa91-e8e54c18cab0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder

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
open GlobalTheory GlobalTheory.SchwartzTranslateUnif
open GlobalTheory.SchwartzTranslate
namespace GlobalTheory.SchwartzTranslateUnif
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (g : 𝓢(V, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g)
      ≤ ‖a‖ * SchwartzMap.seminorm ℂ k (n + 1) g := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have e : ⇑(LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g) = fun y => fderiv ℝ g y a := by
    funext y; rw [LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [e]
  have h1 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖ := by
    rw [← norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_clm_apply_const
      (g.smooth'.fderiv_right (m := ∞) le_rfl).contDiffAt
      (by exact_mod_cast le_top)
  have h2 := SchwartzMap.le_seminorm ℂ k (n + 1) g x
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖x‖ ^ k * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by gcongr
    _ = ‖a‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by ring
    _ ≤ _ := by gcongr
end GlobalTheory.SchwartzTranslateUnif
