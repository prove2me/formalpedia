-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:46.878947+00:00
-- url     : https://prove2.me/submissions/3da32a75-4b60-456a-a34a-116f2c7e458b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_exists_char_of_mul_on_cone
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_char_split
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_IsStrict_add
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_IsStrict_arch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone
namespace GlobalTheory.CompanionTheory.StrictCone
theorem _root_.solution : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  intro a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩
  let S : Set ((Fin a → ℤ) × (Fin b → ℤ)) := {z | IsStrict z.1 ∧ IsStrict z.2}
  obtain ⟨φ, hφ, hfφ⟩ := exists_char_of_mul_on_cone S
    (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2)
    (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne
    (fun g => by
      obtain ⟨K₁, h₁⟩ := IsStrict.arch (s := x₀) hx₀ g.1
      obtain ⟨K₂, h₂⟩ := IsStrict.arch (s := y₀) hy₀ g.2
      refine ⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩
      · exact h₁ _ (by omega)
      · exact h₂ _ (by omega))
  let Q : ℂˣ := Units.mk0 q hq
  obtain ⟨ξa, ha⟩ := char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)
  obtain ⟨ξb, hb⟩ := char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)
  refine ⟨ξa, ξb, fun x y hx hy => ?_⟩
  have h1 : χ x y = (φ (x, y) : ℂ) := hfφ (x, y) ⟨hx, hy⟩
  have h2 : φ (x, y) = φ (x, 0) * φ (0, y) := by rw [← hφ]; simp
  rw [h1, h2, ha x, hb y]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]
end GlobalTheory.CompanionTheory.StrictCone
