-- Prove2me | solution 1 for GlobalTheory.Klein.DiffUnit.disc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:04.775913+00:00
-- url     : https://prove2.me/submissions/a96c922b-0ae1-48d4-b2e9-b410cb479d1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein.DiffUnit
theorem _root_.solution {K : Type*} [Field K] (h r g₂ g₃ P Q y z s t : K) (hh : 2 * h = 1) (hD : P - Q ≠ 0)
    (hy : y ^ 2 = 4 * P ^ 3 - g₂ * P - g₃) (hz : z ^ 2 = 4 * Q ^ 3 - g₂ * Q - g₃)
    (hs : s * (P - Q) = y - z) (ht : t * (P - Q) = y + z) :
    ∃ A B C : K, A = 12 * (P - r) + 12 * r ∧
      B = s * t + (4 * ((Q - r) + 2 * (P - r)) + 12 * r) ∧
      C = h ^ 2 * (s + t) ^ 2 * ((P - r) - (Q - r)) ∧
      g₂ ^ 3 - 27 * g₃ ^ 2 = (P - Q) * (h ^ 4 * (B * (A ^ 2 * (B * ((P - r) - (Q - r)))
        - 16 * (B * ((P - r) - (Q - r))) ^ 2 + 72 * A * (C * ((P - r) - (Q - r))))
        - C * (4 * A ^ 3 + 432 * (C * ((P - r) - (Q - r)))))) := by
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  set B := s * t + (4 * ((Q - r) + 2 * (P - r)) + 12 * r) with hB
  set C := h ^ 2 * (s + t) ^ 2 * ((P - r) - (Q - r)) with hC
  have e1 : B * (P - Q) = 12 * P ^ 2 - g₂ := by
    apply mul_right_cancel₀ hD
    have : (s * (P - Q)) * (t * (P - Q)) = (y - z) * (y + z) := by rw [hs, ht]
    rw [hB]
    linear_combination this + hy - hz
  have e2 : C * (P - Q) = 4 * P ^ 3 - g₂ * P - g₃ := by
    have : (s + t) * (P - Q) = 2 * y := by linear_combination hs + ht
    have h3 : C * (P - Q) = h ^ 2 * ((s + t) * (P - Q)) ^ 2 := by rw [hC]; ring
    rw [h3, this, ← hy]
    linear_combination y ^ 2 * (2 * h + 1) * hh
  have e3 : (P - r) - (Q - r) = P - Q := by ring
  clear_value B C
  rw [e3, e1, e2]
  have e4 : 16 * h ^ 4 = 1 := by
    have : 16 * h ^ 4 = (2 * h) ^ 4 := by ring
    rw [this, hh, one_pow]
  linear_combination -(g₂ ^ 3 - 27 * g₃ ^ 2) * e4
    - h ^ 4 * ((12 * P) ^ 2 * (12 * P ^ 2 - g₂) - 16 * (12 * P ^ 2 - g₂) ^ 2
        + 72 * (12 * P) * (4 * P ^ 3 - g₂ * P - g₃)) * e1
    + h ^ 4 * (4 * (12 * P) ^ 3 + 432 * (4 * P ^ 3 - g₂ * P - g₃)) * e2
end GlobalTheory.Klein.DiffUnit
