-- Prove2me | solution 1 for GlobalTheory.card_fixedBy_pow_prime_pow_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:42.35554+00:00
-- url     : https://prove2.me/submissions/6718bafc-bd8a-4003-a29c-fdd031ec40cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2
end GlobalTheory
