-- Prove2me | solution 1 for GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:44.729606+00:00
-- url     : https://prove2.me/submissions/d60fa353-8e8d-47f2-b053-5f3101f036bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenize
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenizeStatement
import Theorems.Thm_GlobalTheory_exists_isHomogeneous_dehomogenize


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by
  first | exact @GlobalTheory.exists_isHomogeneous_dehomogenize | exact GlobalTheory.exists_isHomogeneous_dehomogenize | (intros; apply GlobalTheory.exists_isHomogeneous_dehomogenize <;> assumption)
end _root_.GlobalTheory.T
