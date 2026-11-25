-- Prove2me | solution 1 for GlobalTheory.SingleBlock.mem_blockPar_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:39.066257+00:00
-- url     : https://prove2.me/submissions/cd3a86de-dcb7-42b4-904c-0f9c3bd76774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
private theorem mem_blockPar_iff' (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔ ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) :=
  Iff.rfl
end GlobalTheory.SingleBlock
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔
      (∃ p ∈ Q, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₁ =
        (p : Matrix (Fin r) (Fin r) k)) ∧
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₁ = 0 := by
  rw [mem_blockPar_iff']
  constructor
  · rintro ⟨p, hp, b, d, e⟩
    exact ⟨⟨p, hp, by rw [e, toBlocks_fromBlocks₁₁]⟩, by rw [e, toBlocks_fromBlocks₂₁]⟩
  · rintro ⟨⟨p, hp, h11⟩, h21⟩
    have hM : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k)
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₂ 0
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂ := by
      rw [← h11, ← h21, fromBlocks_toBlocks]
    have hdet : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂.det ≠ 0 := by
      intro h0
      have hu := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h)).ne_zero
      rw [hM, det_fromBlocks_zero₂₁, h0, mul_zero] at hu
      exact hu rfl
    exact ⟨p, hp, _, Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), hM⟩
end GlobalTheory.SingleBlock
