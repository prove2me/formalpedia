-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.eval_idFrame_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:35.604831+00:00
-- url     : https://prove2.me/submissions/2e4008bb-92fc-448f-9d5c-59ecf96687e0

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution {R : Type*} [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  rw [hw, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, lpMinor, RingHom.map_det]
  have : ∀ (k : ℕ) (h1 : k ≤ r) (h2 : k ≤ n), (eval (idFrame R r n)).mapMatrix
      (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin r × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [idFrame, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one, one_pow]
end GlobalTheory.FockHighestWeight
