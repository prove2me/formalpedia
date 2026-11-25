-- Prove2me | solution 1 for GlobalTheory.CountId.Cm_Yb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:04.323381+00:00
-- url     : https://prove2.me/submissions/3c25265b-e264-499b-84de-cd8800c052d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_vecMul_pow_Yb

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
theorem _root_.solution (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) :
    Cm (Yb e T v l) = Matrix.of fun i j : Fin n => l ((T ^ (i : ℕ)) (e j)) := by
  ext i j
  simp only [Cm, Yb, Matrix.of_apply]
  exact vecMul_pow_Yb e T l i j
end GlobalTheory.CountId
