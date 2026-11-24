-- Prove2me | solution 1 for GlobalTheory.SquareDistanceExpansion.prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:10.08323+00:00
-- url     : https://prove2.me/submissions/b69a8b56-6e54-46f0-9af8-0a70bf426da1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SqId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareDistanceExpansion
open Matrix
namespace GlobalTheory.SquareDistanceExpansion
theorem _root_.solution {R : Type} [CommRing R] {n d : ℕ} (a c : Matrix (Fin n) (Fin d) R)
    (α γ : Matrix (Fin d) (Fin n) R) (M N : Matrix (Fin d) (Fin d) R) :
    a * M * α * (c * N * γ) = a * M * (α * c) * N * γ := by
  simp only [Matrix.mul_assoc]
end GlobalTheory.SquareDistanceExpansion
