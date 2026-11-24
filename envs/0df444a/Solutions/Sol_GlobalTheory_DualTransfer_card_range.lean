-- Prove2me | solution 1 for GlobalTheory.DualTransfer.card_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:04.042551+00:00
-- url     : https://prove2.me/submissions/381ef8d9-1b5f-4e3c-97d2-d03b429c8577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer
namespace GlobalTheory.DualTransfer
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (M : AddSubgroup A) (K : AddSubgroup B) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (f : B →+ AddChar (A ⧸ M) ℂ) (hf : ∀ b (a : A), f b (a : A ⧸ M) = e a b) :
    Nat.card f.range = Nat.card (B ⧸ K) := by
  have hker : f.ker = K := by
    ext b
    rw [AddMonoidHom.mem_ker, hK, AddChar.eq_zero_iff]
    constructor
    · intro h a
      rw [← hf]
      exact h _
    · intro h q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [hf]
      exact h a
  rw [← hker]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv).symm
end GlobalTheory.DualTransfer
