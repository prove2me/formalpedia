-- Prove2me | solution 1 for GlobalTheory.CountId.toMatrix_tw_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:25.723134+00:00
-- url     : https://prove2.me/submissions/ec975240-c3b1-46a1-9426-bad626c4f0a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_tw_repr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    (tw e γ).toMatrix e = (γ : Matrix (Fin n) (Fin n) E) := by
  ext i j
  rw [Basis.toMatrix_apply, congrFun (tw_repr e γ (e j)) i]
  simp [Basis.repr_self, Finsupp.single_apply, Matrix.mulVec, dotProduct]
end GlobalTheory.CountId
