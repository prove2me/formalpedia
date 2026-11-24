-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:34.650365+00:00
-- url     : https://prove2.me/submissions/b239201f-710f-4990-9dbb-d4b2b3f3626c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_contDiff_phaseLine
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_norm_iteratedDeriv_phaseLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open Complex
open GlobalTheory GlobalTheory.LinPhaseSeminorm
namespace GlobalTheory.LinPhaseSeminorm
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c t : ℝ) : Function.HasTemperateGrowth (phaseLine c t ∘ ⇑L) := by
  refine ⟨(contDiff_phaseLine c t).comp L.contDiff, fun n => ⟨0, (2 * Real.pi * |t| * ‖L‖) ^ n, fun x => ?_⟩⟩
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := n) (by exact_mod_cast le_top),
    pow_zero, mul_one]
  calc _ ≤ ‖iteratedFDeriv ℝ n (phaseLine c t) (L x)‖ * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp [mul_pow]
end GlobalTheory.LinPhaseSeminorm
