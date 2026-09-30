-- Prove2me | solution 1 for Lubbecke2005.SubcolumnPricing.strictly_redundant_not_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:45:42.050503+00:00
-- url     : https://prove2.me/submissions/cd8f0ab2-e197-4faa-a503-198776d88c85

import Mathlib
import Definitions.Def_Lubbecke2005_SubcolumnPricing_Columns
open Lubbecke2005.SubcolumnPricing

private theorem incidence_sum {m : ℕ} (s : Finset (Fin m)) :
    (∑ i, incidence s i) = (s.card : ℝ) := by
  simp [incidence]

private theorem one_dot_incidence {m : ℕ} (s : Finset (Fin m)) :
    (1 : Fin m → ℝ) ⬝ᵥ incidence s = (s.card : ℝ) := by
  simpa [dotProduct] using incidence_sum s

theorem solution {m : ℕ} (𝒜 : Finset (Finset (Fin m)))
    (c : Finset (Fin m) → ℝ) (u : Fin m → ℝ)
    (h𝒜 : ∅ ∉ 𝒜) (hsub : SubcolumnProperty 𝒜 c)
    (s : Finset (Fin m)) (hs : s ∈ 𝒜) (hred : IsStrictlyRedundant 𝒜 c s) :
    ¬ (∀ a ∈ 𝒜, pricingRatio c u s ≤ pricingRatio c u a) := by
  intro hopt
  obtain ⟨lam, hlam, hvec, hcost⟩ := hred
  have hpos (a : Finset (Fin m)) (ha : a ∈ 𝒜) : 0 < (a.card : ℝ) := by
    have hne : a ≠ ∅ := by intro he; subst a; exact h𝒜 ha
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hmass : (∑ r ∈ 𝒜.filter (· ⊂ s), lam r * (r.card : ℝ)) = (s.card : ℝ) := by
    have hh := congrArg (fun v : Fin m → ℝ => (1 : Fin m → ℝ) ⬝ᵥ v) hvec
    simpa only [dotProduct_sum, dotProduct_smul, smul_eq_mul, one_dot_incidence] using hh
  have hdot : (∑ r ∈ 𝒜.filter (· ⊂ s), lam r * (u ⬝ᵥ incidence r)) = u ⬝ᵥ incidence s := by
    have hh := congrArg (fun v : Fin m → ℝ => u ⬝ᵥ v) hvec
    simpa only [dotProduct_sum, dotProduct_smul, smul_eq_mul] using hh
  have hsum :
      (∑ r ∈ 𝒜.filter (· ⊂ s), lam r * ((c s - u ⬝ᵥ incidence s) * (r.card : ℝ))) ≤
      ∑ r ∈ 𝒜.filter (· ⊂ s), lam r * ((c r - u ⬝ᵥ incidence r) * (s.card : ℝ)) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrA := (Finset.mem_filter.mp hr).1
    have hh := hopt r hrA
    simp only [pricingRatio, one_dot_incidence] at hh
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff₀ (hpos s hs) (hpos r hrA)).mp hh) (hlam r)
  have hsum' : (c s - u ⬝ᵥ incidence s) * (∑ r ∈ 𝒜.filter (· ⊂ s), lam r * (r.card : ℝ)) ≤
      ((∑ r ∈ 𝒜.filter (· ⊂ s), c r * lam r) -
        (∑ r ∈ 𝒜.filter (· ⊂ s), lam r * (u ⬝ᵥ incidence r))) * (s.card : ℝ) := by
    convert hsum using 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
  rw [hmass, hdot] at hsum'
  nlinarith [hpos s hs]
