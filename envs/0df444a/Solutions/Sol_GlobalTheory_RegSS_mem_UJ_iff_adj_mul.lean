-- Prove2me | solution 1 for GlobalTheory.RegSS.mem_UJ_iff_adj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:59.195398+00:00
-- url     : https://prove2.me/submissions/4f0a7948-ab30-4472-a6f8-4f40fe816251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CentralizerTensorForms_adj_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ UJ σ J ↔ adj σ J (g : Matrix n n A) * (g : Matrix n n A) = 1 := by
  change cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J ↔ _
  rw [(adj_eq_iff σ hJ (g : Matrix n n A) _).1 rfl, Matrix.mul_assoc]
  constructor
  · intro h
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).mul_left_cancel (by rw [h, mul_one])
  · intro h; rw [h, Matrix.mul_one]
end GlobalTheory.RegSS
