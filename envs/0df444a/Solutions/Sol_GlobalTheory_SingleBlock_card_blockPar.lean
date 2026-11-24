-- Prove2me | solution 1 for GlobalTheory.SingleBlock.card_blockPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:06.408551+00:00
-- url     : https://prove2.me/submissions/bb12128c-604b-4728-a5b7-b34d00cf5229

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
theorem _root_.solution (Q : Subgroup (GL (Fin r) k)) :
    Nat.card (blockPar t Q) =
      Nat.card Q * (Nat.card k ^ (r * t) * Nat.card (GL (Fin t) k)) := by
  let φ : Q × (Matrix (Fin r) (Fin t) k × GL (Fin t) k) → blockPar t Q := fun x =>
    ⟨blockUnit x.1.1 x.2.1 x.2.2, (mem_blockPar_iff' Q _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨p, hp⟩, b, d⟩ ⟨⟨p', hp'⟩, b', d'⟩ h
      have h1 : fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) =
          fromBlocks (p' : Matrix (Fin r) (Fin r) k) b' 0 (d' : Matrix (Fin t) (Fin t) k) :=
        congrArg (fun z : blockPar t Q =>
          ((z : GL (Fin r ⊕ Fin t) k) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k)) h
      obtain ⟨e1, e2, -, e4⟩ := Matrix.fromBlocks_inj.mp h1
      have hp_eq : p = p' := Units.ext e1
      have hd_eq : d = d' := Units.ext e4
      subst hp_eq hd_eq e2
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨p, hp, b, d, e⟩ := (mem_blockPar_iff' Q h).mp hh
      exact ⟨(⟨p, hp⟩, b, d), Subtype.ext (Units.ext e.symm)⟩
  have hM : Nat.card (Matrix (Fin r) (Fin t) k) = Nat.card k ^ (r * t) := by
    show Nat.card (Fin r → Fin t → k) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card (α := Fin t), Nat.card_eq_fintype_card (α := Fin r),
      Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm t r]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod, hM]
end GlobalTheory.SingleBlock
