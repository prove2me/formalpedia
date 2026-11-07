-- Prove2me | solution 1 for NaturalProofs.distC_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:20.96054+00:00
-- url     : https://prove2.me/submissions/1bf49147-fb40-4ecb-a117-a15885419674

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_walkC_size
public import Theorems.Thm_NaturalProofs_MCircuit_comp_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_size
public import Theorems.Thm_NaturalProofs_MCircuit_ofCircuit_size
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_size_le
public import Theorems.Thm_NaturalProofs_MCircuit_toCircuit_size


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution {k n B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool)) :
    (distC gc hk i e c D).size ≤ 2 ^ n * (n * (2 * k * B + 4 * k)) + D.size := by
  have hleaf : ∀ x : Fin n → Bool, (leafC gc hk i e c x).size ≤ n * (2 * k * B + 4 * k) := by
    intro x
    have := walkC_size gc hB (startC i e c x) (((List.ofFn x).drop (i + 1)).map Sum.inr)
    have h0 : (startC (k := k) i e c x).size = 0 := by
      unfold startC
      dsimp only
      split <;> rfl
    have hl : (((List.ofFn x).drop (i + 1)).map (Sum.inr : Bool → Fin (2 * k) ⊕ Bool)).length ≤ n := by
      simp
    simp only [leafC, mapOut_size, h0, zero_add] at this ⊢
    exact this.trans (Nat.mul_le_mul_right _ hl)
  have := parAll_size_le (leafC gc hk i e c) _ hleaf
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  simp only [distC, toCircuit_size, comp_size, ofCircuit_size]
  omega
end NaturalProofs
