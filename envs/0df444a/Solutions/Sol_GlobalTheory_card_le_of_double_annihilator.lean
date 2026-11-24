-- Prove2me | solution 1 for GlobalTheory.card_le_of_double_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:48.8748+00:00
-- url     : https://prove2.me/submissions/4c649157-ef16-4a75-a3e6-526f852ed32a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardLeOfDoubleAnnihilatorPairing

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
theorem _root_.solution (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X]
    (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O)
    (h1 : ∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S)
    (h2 : ∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0)
    (h3 : ∀ e : E, a • e = 0 → e ∈ Es) :
    Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  classical
  let L : X →ₗ[O] (F → E) :=
    LinearMap.pi fun y => if (∀ s ∈ S, β (y : Y) s = 0) then β y else 0
  have hL : ∀ x (y : F), L x y = if (∀ s ∈ S, β (y : Y) s = 0) then β y x else 0 := by
    intro x y
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hS : S ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext y
    rw [hL]
    split_ifs with h
    · exact h x hx
    · rfl
  have hker : LinearMap.ker L ≤ S := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply h1
    intro y hy
    have := congrFun hx ⟨y, (h2 y hy).1⟩
    rw [hL, if_pos hy] at this
    exact this
  have hmem : ∀ x (y : F), L x y ∈ Es := by
    intro x y
    apply h3
    rw [hL]
    split_ifs with h
    · rw [← LinearMap.smul_apply, ← map_smul, (h2 y h).2, map_zero, LinearMap.zero_apply]
    · exact smul_zero a
  let g : X ⧸ S → (F → Es) := fun q y =>
    ⟨S.liftQ L hS q y, by
      induction q using Submodule.Quotient.induction_on with
      | H x => simpa using hmem x y⟩
  have hinj : Function.Injective g := by
    intro q r hqr
    have h' : S.liftQ L hS q = S.liftQ L hS r := by
      funext y
      have := congrFun hqr y
      simpa [g] using congrArg Subtype.val this
    exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot S L hS hker)) h'
  have hq : Nat.card (X ⧸ S) ≤ Es.card ^ F.card := by
    have := Nat.card_le_card_of_injective g hinj
    rwa [Nat.card_fun, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard] at this
  rw [Submodule.card_eq_card_quotient_mul_card S, mul_comm]
  exact Nat.mul_le_mul_right _ hq
end GlobalTheory
