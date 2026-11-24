-- Prove2me | solution 1 for GlobalTheory.StdLoc.mem_blockPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:33.445721+00:00
-- url     : https://prove2.me/submissions/7eab2836-33e7-4992-a73e-2d5b043ad1db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.StdLoc
namespace GlobalTheory.StdLoc
namespace _root_.GlobalTheory.StdLoc
theorem _root_.solution {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by
  show (g : Matrix (Fin d) (Fin d) R).BlockTriangular (_root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom a) ↔ _
  unfold Matrix.BlockTriangular _root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom
  constructor
  · intro h i j hj hi
    apply h
    simp [hi, not_le.mpr hj]
  · intro h i j hlt
    refine h i j ?_ ?_ <;> split_ifs at hlt <;> omega
end _root_.GlobalTheory.StdLoc
end GlobalTheory.StdLoc
