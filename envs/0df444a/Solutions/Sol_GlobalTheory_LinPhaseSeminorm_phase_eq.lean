-- Prove2me | solution 1 for GlobalTheory.LinPhaseSeminorm.phase_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:07.561463+00:00
-- url     : https://prove2.me/submissions/d885ce28-1bcc-4f18-9b81-6a20bda98c18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe

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
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c t : ℝ) :
    (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = phaseLine c t ∘ ⇑L := by
  funext x
  simp only [phaseLine, Function.comp_apply, ← Complex.exp_add]
  congr 1; push_cast; ring
end GlobalTheory.LinPhaseSeminorm
