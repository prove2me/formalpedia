-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.card_le_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:17.12865+00:00
-- url     : https://prove2.me/submissions/089291e7-c84d-4e7f-ac8d-38863e8e5025

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have hne : ∀ x y, b x y ≠ 0 := fun x y h => by
    have := hn x y
    simp [h] at this
  have h0 : ∀ x, b x 0 = 1 := fun x => by
    have := hr x 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne x 0)).1 this.symm
  let f : A → AddChar B ℂ := fun x =>
    { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }
  have hf : Function.Injective f := by
    intro x x' h
    have e : ∀ y, b x y = b x' y := fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h
    have : x - x' = 0 := hk _ fun y => by
      have h1 := hl (x - x') x' y
      rw [sub_add_cancel, e y] at h1
      exact (mul_eq_right₀ (hne x' y)).1 h1.symm
    exact sub_eq_zero.1 this
  have e : Nat.card (AddChar B ℂ) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  exact e ▸ Nat.card_le_card_of_injective f hf
end GlobalTheory.CompanionTheory.SW.CofinalDual
