-- Prove2me | solution 1 for MultiwayCut.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:24:02.034886+00:00
-- url     : https://prove2.me/submissions/a1e9ae7c-c6fa-43ed-9304-042cfd3ce259

import Mathlib
import Definitions.Def_MultiwayCut_Transformation

open Matrix

namespace Aux_MWC53

theorem aux : ∀ (k : ℕ) (a u : Fin k → ℝ), Antitone u → (∀ ℓ, 0 ≤ u ℓ) →
    (∀ ℓ, 0 ≤ ∑ j ∈ Finset.Iic ℓ, a j) → 0 ≤ ∑ j, a j * u j := by
  intro k
  induction k with
  | zero => intro a u _ _ _; simp
  | succ k ih =>
    intro a u hu hu0 ha
    obtain ⟨c, hc⟩ : ∃ c, c = u (Fin.last k) := ⟨_, rfl⟩
    have e : ∑ j : Fin k, a j.castSucc * (u j.castSucc - c) =
        ∑ j : Fin k, a j.castSucc * u j.castSucc - ∑ j : Fin k, c * a j.castSucc := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsplit : ∑ j, a j * u j =
        ∑ j : Fin k, a j.castSucc * (u j.castSucc - c) + c * ∑ j, a j := by
      rw [e, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (f := a), mul_add, Finset.mul_sum, ← hc]
      ring
    have hIH := ih (fun j => a j.castSucc) (fun j => u j.castSucc - c)
      (fun i j hij => by
        have := hu (Fin.castSucc_le_castSucc_iff.2 hij)
        linarith)
      (fun ℓ => by
        have := hu (Fin.le_last ℓ.castSucc)
        linarith)
      (fun ℓ => by
        have := ha ℓ.castSucc
        rw [← Fin.map_castSuccEmb_Iic, Finset.sum_map] at this
        exact this)
    have hall : 0 ≤ ∑ j, a j := by
      have := ha (Fin.last k)
      have hI : Finset.Iic (Fin.last k) = Finset.univ := by
        ext j; simp [Fin.le_last]
      rwa [hI] at this
    have hc0 : 0 ≤ c := by rw [hc]; exact hu0 _
    rw [hsplit]
    have := mul_nonneg hc0 hall
    linarith

end Aux_MWC53

open MultiwayCut in
theorem solution {k : ℕ} (a : Fin k → ℝ) :
    (∀ u : Fin k → ℝ, Antitone u → (∀ ℓ, 0 ≤ u ℓ) → 0 ≤ a ⬝ᵥ u) ↔ MultiwayCut.PrefixGe a 0 := by
  constructor
  · intro h ℓ
    have hu := h (fun j => if j ≤ ℓ then 1 else 0)
      (fun i j hij => by
        dsimp only
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd (hij.trans h1) h2
        · norm_num
        · exact le_rfl)
      (fun j => by split_ifs <;> norm_num)
    simp only [dotProduct, mul_ite, mul_one, mul_zero] at hu
    rw [← Finset.sum_filter] at hu
    have hI : Finset.univ.filter (fun j => j ≤ ℓ) = Finset.Iic ℓ := by
      ext j; simp
    rw [hI] at hu
    simpa using hu
  · intro h u hu hu0
    have := Aux_MWC53.aux k a u hu hu0 (fun ℓ => by
      have := h ℓ
      simpa using this)
    exact this
