-- Prove2me | solution 1 for GlobalTheory.CountId.exists_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:04.658566+00:00
-- url     : https://prove2.me/submissions/5e74d14b-a5a6-4152-929a-2d76982446c1

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
theorem _root_.solution (e e' : Basis (Fin n) E V) : ∃ γ : GL (Fin n) E, tw e γ = e' := by
  refine ⟨⟨e'.toMatrix e, e.toMatrix e', Basis.toMatrix_mul_toMatrix_flip e' e,
    Basis.toMatrix_mul_toMatrix_flip e e'⟩,
    Basis.repr_injective (LinearEquiv.ext fun x => Finsupp.ext fun i => ?_)⟩
  rw [congrFun (tw_repr e _ x) i]
  simp [Basis.toMatrix_mulVec_repr]
end GlobalTheory.CountId
