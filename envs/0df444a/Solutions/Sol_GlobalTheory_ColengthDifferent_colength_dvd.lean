-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.colength_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:13.849425+00:00
-- url     : https://prove2.me/submissions/338551cb-9569-48b6-8046-591f002deaec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
import Theorems.Thm_GlobalTheory_ColengthDifferent_colength_dvd_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution : ∀ (E F T : Type) [Field E] [NumberField E] [Field F] [CharZero F] [CommRing T] [IsDomain T] [Algebra T F] [IsFractionRing T F] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι → (𝓞 E →+* T)) (m : ι → ℕ) (g : ℕ) (e : Fin g ≃ Σ i : ι, Fin (m i)) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T) (u : ∀ i, Fin (m i) → (Fin g → T)), Function.Injective τ → Fintype.card ι = Module.finrank ℚ E → IsIntegrallyClosed T → (∀ i (w : Fin g → T), (∀ a, (A a).mulVec w = τ i a • w) → ∃ cf : Fin (m i) → T, w = ∑ k, cf k • u i k) → (∀ i k a, (A a).mulVec (u i k) = τ i a • u i k) → ∀ δ : ι → 𝓞 E, (∀ i, δ i ∈ differentIdeal ℤ (𝓞 E)) → (Matrix.of fun j k : Fin g => u (e j).1 (e j).2 k).det ∣ ∏ i, τ i (δ i) ^ m i := by
  intro E F T _ _ _ _ _ _ _ _ ι _ _ τ m g e A u hτ hcard _ hsp _ δ hδ
  classical
  by_cases hz : ∃ i, δ i = 0 ∧ m i ≠ 0
  · obtain ⟨i, hi, hm⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, map_zero, zero_pow hm])]
    exact dvd_zero _
  · push Not at hz
    obtain ⟨δ₀, hδ₀, hδ₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
    let δ' : ι → 𝓞 E := fun i => if δ i = 0 then δ₀ else δ i
    have h := colength_dvd_of_ne_zero F T ι τ m g e A u hτ hcard hsp δ'
      (fun i => by simp only [δ']; split_ifs; exacts [hδ₀, hδ i])
      (fun i => by simp only [δ']; split_ifs with h; exacts [hδ₀0, h])
    have hp : ∏ i, τ i (δ i) ^ m i = ∏ i, τ i (δ' i) ^ m i :=
      Finset.prod_congr rfl fun i _ => by
        by_cases h0 : δ i = 0
        · rw [hz i h0, pow_zero, pow_zero]
        · simp only [δ', if_neg h0]
    rw [hp]
    exact h
end GlobalTheory.ColengthDifferent
