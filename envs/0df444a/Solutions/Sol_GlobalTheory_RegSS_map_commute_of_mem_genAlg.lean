-- Prove2me | solution 1 for GlobalTheory.RegSS.map_commute_of_mem_genAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:21:55.147804+00:00
-- url     : https://prove2.me/submissions/88fb6478-8f0f-4025-abc2-9383c2131afd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B) {M l : Matrix n n A}
    {N : Matrix n n B} (h : N * M.map f = M.map f * N) (hl : l ∈ genAlg M) :
    N * l.map f = l.map f * N := by
  unfold genAlg at hl
  induction hl using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap r =>
    have : (algebraMap A (Matrix n n A) r).map f = f r • (1 : Matrix n n B) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; simp
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add f), Matrix.mul_add, Matrix.add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, ← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]
end GlobalTheory.RegSS
