-- Prove2me | solution 1 for GlobalTheory.CountId.tw_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:27.238394+00:00
-- url     : https://prove2.me/submissions/74ebad0b-05c2-4aa7-8072-5764137f8d8f

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
theorem _root_.solution (e : Basis (Fin n) E V) (γ δ : GL (Fin n) E) : tw (tw e γ) δ = tw e (δ * γ) := by
  have key : ∀ (b : Basis (Fin n) E V) (g : GL (Fin n) E) (y : V) (i : Fin n),
      (tw b g).repr y i = ((g : Matrix (Fin n) (Fin n) E) *ᵥ fun i => b.repr y i) i :=
    fun b g y i => congrFun (tw_repr b g y) i
  refine Basis.repr_injective (LinearEquiv.ext fun x => Finsupp.ext fun i => ?_)
  simp only [key, Units.val_mul, Matrix.mulVec_mulVec]
end GlobalTheory.CountId
