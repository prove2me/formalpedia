-- Prove2me | solution 1 for GlobalTheory.lagrRankOne_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:31.649062+00:00
-- url     : https://prove2.me/submissions/7d92a121-7b62-4bdd-bbd7-3c6e15b38689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hS : Sᵀ = -S.map c) (j : Fin n) :
    (lagrRankOne S j)ᵀ * S + S * (lagrRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, lagrRankOne, h3, h1]
end GlobalTheory
