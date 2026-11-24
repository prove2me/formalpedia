-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.norm_psi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:07.003252+00:00
-- url     : https://prove2.me/submissions/1e43f226-582c-4e28-a11e-114a93c07cbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz
namespace GlobalTheory.PhaseLipschitz
theorem _root_.solution (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
end GlobalTheory.PhaseLipschitz
