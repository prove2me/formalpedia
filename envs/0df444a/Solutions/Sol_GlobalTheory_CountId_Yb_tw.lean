-- Prove2me | solution 1 for GlobalTheory.CountId.Yb_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:25.322032+00:00
-- url     : https://prove2.me/submissions/fd35af70-3ce4-4b7e-82ee-33078ec426f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_tw_apply
import Theorems.Thm_GlobalTheory_CountId_tw_repr
import Theorems.Thm_GlobalTheory_CountId_toMatrix_tw_left
import Theorems.Thm_GlobalTheory_CountId_toMatrix_tw_right

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
theorem _root_.solution (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) (γ : GL (Fin n) E) :
    Yb (tw e γ) T v l = act γ (Yb e T v l) := by
  simp only [Yb, act]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (tw e γ) e (tw e γ) e,
      toMatrix_tw_left, toMatrix_tw_right]
  · exact tw_repr e γ v
  · funext j
    simp [tw_apply, map_sum, Matrix.vecMul, dotProduct, mul_comm]
end GlobalTheory.CountId
