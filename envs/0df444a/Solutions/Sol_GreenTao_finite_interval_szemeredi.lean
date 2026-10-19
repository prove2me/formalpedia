-- Prove2me | solution 1 for GreenTao.finite_interval_szemeredi
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T20:37:20.47951+00:00
-- url     : https://prove2.me/submissions/e21e449b-7f43-45b9-af48-7e878a71bf70

import Theorems.Thm_Erdos142_erdos_139_szemeredi

open scoped BigOperators Topology
open Filter

/-- The finite-interval existence input in the classical Varnavides argument.
Source: Green--Tao, Proposition 2.1; the existing platform Szemerédi theorem
supplies the density threshold. -/
theorem solution (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, k ≤ L ∧
      ∀ S : Finset ℕ, S ⊆ Finset.range L → δ * (L : ℝ) ≤ (S.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < L ∧
          ∀ j < k, a + j * d ∈ S := by
  classical
  have hlim := Erdos142.erdos_139_szemeredi k (by omega)
  have hsmall : ∀ᶠ N : ℕ in atTop, (Erdos142.r k N : ℝ) / N < δ :=
    hlim.eventually (eventually_lt_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  let L := max N k
  have hL : 0 < L := by dsimp [L]; omega
  have hLδ : (Erdos142.r k L : ℝ) < δ * (L : ℝ) := by
    have := hN L (by dsimp [L]; omega)
    rwa [div_lt_iff₀ (by exact_mod_cast hL)] at this
  refine ⟨L, by dsimp [L]; omega, ?_⟩
  intro S hS hScard
  by_contra hno
  let T : Finset ℕ := S.image (fun x => x + 1)
  have hT : T ⊆ Finset.Icc 1 L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyL := Finset.mem_range.mp (hS hy)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hTcard : T.card = S.card := by
    exact Finset.card_image_of_injective _ (fun _ _ h => by omega)
  have hfree : Erdos142.IsAPOfLengthFree (T : Set ℕ) k := by
    intro U hU hAP
    obtain ⟨a, d, hcard, hset⟩ := hAP
    have hmem (j : ℕ) (hj : j < k) : a + j * d ∈ T := by
      apply hU
      rw [hset]
      exact ⟨j, by exact_mod_cast hj, by simp [smul_eq_mul]⟩
    by_cases hd : d = 0
    · have hsub : U ⊆ {a} := by
        rw [hset]
        rintro x ⟨j, hj, rfl⟩
        simp [hd]
      rw [← hcard, ENat.card_coe_set_eq]
      exact (Set.encard_mono hsub).trans (by simp)
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have ha : 1 ≤ a := by
        have haT := hmem 0 (by omega)
        simp only [zero_mul, add_zero] at haT
        exact (Finset.mem_Icc.mp (hT haT)).1
      have hback (j : ℕ) (hj : j < k) : (a - 1) + j * d ∈ S := by
        obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (hmem j hj)
        have heq' : y = (a - 1) + j * d := by omega
        simpa [heq'] using hy
      have hlast : (a - 1) + (k - 1) * d < L :=
        Finset.mem_range.mp (hS (hback (k - 1) (by omega)))
      exact False.elim (hno ⟨a - 1, d, hdpos, hlast, hback⟩)
  have hle : S.card ≤ Erdos142.r k L := by
    rw [← hTcard]
    exact Erdos142.le_r hT hfree
  have hle' : (S.card : ℝ) ≤ Erdos142.r k L := by exact_mod_cast hle
  linarith
