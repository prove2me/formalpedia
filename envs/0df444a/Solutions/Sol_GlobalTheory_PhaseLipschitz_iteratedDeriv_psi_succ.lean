-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.iteratedDeriv_psi_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:06.168399+00:00
-- url     : https://prove2.me/submissions/d3ee69e4-fd6b-41fc-8563-47393501b3a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_LinPhaseSeminorm_iteratedDeriv_const_mul_cexp


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
theorem _root_.solution (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]
end GlobalTheory.PhaseLipschitz
