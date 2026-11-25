-- Prove2me | solution 1 for GlobalTheory.CountId.Cm_mul_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:11.312424+00:00
-- url     : https://prove2.me/submissions/c1657b18-ee7e-4198-8d14-707a2e772ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

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
theorem _root_.solution {k : Type} [CommRing k] (Y : Gl n k) :
    Cm Y * Bm Y = Matrix.of fun i j : Fin n => mom Y ((i : ℕ) + (j : ℕ)) := by
  ext i j
  simp only [Matrix.mul_apply, Cm, Bm, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rfl
end GlobalTheory.CountId
