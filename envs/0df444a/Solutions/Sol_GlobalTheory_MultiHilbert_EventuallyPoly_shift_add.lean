-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.EventuallyPoly.shift_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:29.945955+00:00
-- url     : https://prove2.me/submissions/bd0679b5-8b04-4f53-aa85-7dbe8b6dc315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_eval_aeval_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
namespace GlobalTheory.MultiHilbert
namespace EventuallyPoly
theorem _root_.solution {f : (Fin r → ℕ) → ℚ} (hf : EventuallyPoly f) (e : Fin r → ℕ) :
    EventuallyPoly (fun n => f (n + e)) := by
  obtain ⟨Φ, a, h⟩ := hf
  refine ⟨aeval (fun k => X k + C (e k : ℚ)) Φ, a, fun n hn => ?_⟩
  beta_reduce
  rw [eval_aeval_coord, h (n + e) (fun k => (hn k).trans (Nat.le_add_right _ _))]
  simp
end EventuallyPoly
end GlobalTheory.MultiHilbert
