-- Prove2me | solution 1 for GlobalTheory.StdLoc.card_blockPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:54.736281+00:00
-- url     : https://prove2.me/submissions/87679c5c-a0d3-4b56-81f6-453e67ef2ea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL
import Theorems.Thm_GlobalTheory_StdLoc_blockParMk_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.StdLoc
namespace GlobalTheory.StdLoc
theorem _root_.solution (R : Type) [CommRing R] [Finite R] (a d : ℕ) (h : a ≤ d) :
    Nat.card (blockPar R a d) =
      Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ← Nat.card_eq_of_bijective _ blockParMk_bijective, Nat.card_prod, Nat.card_prod,
    mul_assoc]
  congr 2
  show Nat.card (Fin a → Fin b → R) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]
end GlobalTheory.StdLoc
