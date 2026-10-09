-- Prove2me | solution 1 for OAI.Erdos3.exists_preparedRelative_candidate_input_powers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:00:17.211038+00:00
-- url     : https://prove2.me/submissions/4e92c909-af45-4910-b002-4070891305c2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem early_input_components {p t c z r B : ℝ} (s : ℕ)
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hc : 0 ≤ c) (hz : 0 ≤ z) (hr : 0 ≤ r)
    (hB : r + 2 * z + ((s : ℝ) + 2) * c + 6 * t + p + s + 60 ≤ B) :
    z ≤ B ∧ r ≤ B ∧ p + 16 + ((s : ℝ) + 1) * c + z ≤ B ∧
      c + 1 ≤ B ∧ 6 * t + 35 ≤ B := by
  have hsc : 0 ≤ (s : ℝ) * c := mul_nonneg (Nat.cast_nonneg s) hc
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]

theorem exists_preparedRelative_candidate_input_powers
    (s relativePower childExponent normalizationPower regularityPower : ℕ) :
    ∃ basePower precisionPower : ℕ, 2 ≤ basePower ∧ 2 ≤ precisionPower ∧
    ∀ {p vars : ℝ}, 0 ≤ p → 0 ≤ vars → vars ≤ (p + 2) ^ relativePower →
      let pRelative := (p + 2) ^ relativePower
      let childCost := (pRelative + 4) ^ childExponent
      let normBudget := (childCost + vars + 4) ^ normalizationPower
      let Bstruct := (p + 2) ^ basePower
      normBudget ≤ Bstruct ∧ (normBudget + 2) ^ regularityPower ≤ Bstruct ∧
        p + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ Bstruct ∧
        childCost + 1 ≤ Bstruct ∧ 6 * pRelative + 35 ≤ Bstruct ∧
        3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
  let X : Polynomial ℕ := Polynomial.X
  let t := (X + 2) ^ relativePower
  let c := (t + 4) ^ childExponent
  let z := (c + t + 4) ^ normalizationPower
  let r := (z + 2) ^ regularityPower
  let P := r + 2 * z + (Polynomial.C s + 2) * c + 6 * t + X + Polynomial.C s + 60
  obtain ⟨basePower, hbase, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  obtain ⟨precisionPower, hprecision, herror⟩ :=
    exists_natPolynomial_fixed_power_budget (3 * t + 130)
  refine ⟨basePower, precisionPower, hbase, hprecision, ?_⟩
  intro p vars hp hv hvt pRelative childCost normBudget Bstruct
  let zBound := (childCost + pRelative + 4) ^ normalizationPower
  let rBound := (zBound + 2) ^ regularityPower
  have ht0 : 0 ≤ pRelative := by dsimp only [pRelative]; positivity
  have hc0 : 0 ≤ childCost := by dsimp only [childCost]; positivity
  have hz0 : 0 ≤ zBound := by dsimp only [zBound]; positivity
  have hr0 : 0 ≤ rBound := by dsimp only [rBound]; positivity
  have hn0 : 0 ≤ normBudget := by dsimp only [normBudget]; positivity
  have hn : normBudget ≤ zBound :=
    pow_le_pow_left₀ (by positivity : 0 ≤ childCost + vars + 4)
      (by linarith only [hvt] : childCost + vars + 4 ≤ childCost + pRelative + 4) _
  have hreg : (normBudget + 2) ^ regularityPower ≤ rBound :=
    pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl (2 : ℝ))) _
  have hb : rBound + 2 * zBound + ((s : ℝ) + 2) * childCost + 6 * pRelative + p + s + 60 ≤ Bstruct := by
    simpa only [P, r, z, c, t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
      Nat.coe_castRingHom, rBound, zBound, childCost, pRelative, Bstruct] using hbound p hp
  have herr : 3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
    simpa only [t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat, pRelative] using herror p hp
  obtain ⟨hz, hr, hm, hc, ht⟩ := early_input_components s hp ht0 hc0 hz0 hr0 hb
  exact ⟨hn.trans hz, hreg.trans hr,
    (add_le_add (le_refl _) hn).trans hm, hc, ht, herr⟩

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_preparedRelative_candidate_input_powers := @OAI.Erdos3.exists_preparedRelative_candidate_input_powers
