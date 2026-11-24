-- Prove2me | solution 1 for GlobalTheory.Doubling.det_quot_mul_det_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:27.348132+00:00
-- url     : https://prove2.me/submissions/446e7fec-11c4-4f22-86f4-d462872c96d5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_quot_levi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
namespace GlobalTheory.Doubling
theorem _root_.solution {σ : A →+* A} {J : Matrix n n A} (hJ : IsUnit J.det) {M : Matrix ι ι A}
    (hM : cT σ M * dblGram e J * M = dblGram e J) (h : KeepsDiag e M) :
    σ (quotMat e M).det * (leviMat e M).det = 1 := by
  have h1 := congrArg det (quot_levi e hM h)
  rw [det_mul, det_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  exact hJ.mul_left_cancel (by linear_combination h1)
end GlobalTheory.Doubling
