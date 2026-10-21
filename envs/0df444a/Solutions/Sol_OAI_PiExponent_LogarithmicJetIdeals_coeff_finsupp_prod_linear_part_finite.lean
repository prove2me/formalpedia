-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part_finite
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:12:54.706721+00:00
-- url     : https://prove2.me/submissions/fadc44b1-d9a1-42ae-97bd-127fed0ccf25

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.Data.Finsupp.Weight

/-!
# Coefficients of a finite product at total degree equal to the number of factors

Let `R j` be a family of multivariate power series over a commutative semiring `K`,
indexed by a finite type `σ`, and suppose that each `R j` has the same coefficients
as the variable `X (v j)` in total degrees `0` and `1`.  Then the coefficient of
`∏ j, R j` at any exponent of total degree `card σ` agrees with the coefficient of
`∏ j, X (v j)`.

The proof does not use subtraction (the coefficient ring is only a commutative
semiring).  It rests on two observations:

* A product of `n` series with vanishing constant term has no coefficients in total
  degree below `n` (proved by induction on the finite index set, using the
  convolution formula for coefficients).
* Consequently, in the coefficient of the product of `n` series at total degree
  `n`, every factor must contribute total degree exactly `1`; those coefficients
  agree by hypothesis, while all other contributions vanish.

Both facts are formalized as the lemmas `coeff_prod_eq_zero_of_lt_card` and
`coeff_prod_eq_of_linear_agree`, and the theorem follows by applying the second
with `s = univ` and `g j = X (v j)`.
-/

open scoped BigOperators

noncomputable section
open scoped BigOperators

namespace ProdLinear

/-- A product of `s.card` series all with vanishing constant term has no coefficients
in total degree below `s.card`. -/
lemma coeff_prod_eq_zero_of_lt_card
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ] :
    ∀ (s : Finset σ) (f : σ → MvPowerSeries ι K),
      (∀ j, MvPowerSeries.coeff 0 (f j) = 0) →
      ∀ d : ι →₀ ℕ, Finsupp.degree d < s.card →
        MvPowerSeries.coeff d (∏ j ∈ s, f j) = 0 := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro f hf d hd
      simp only [Finset.card_empty] at hd
      omega
  | cons a s ha ih =>
      intro f hf d hd
      rw [Finset.card_cons ha] at hd
      rw [Finset.prod_cons ha]
      rw [MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨d1, d2⟩ := p
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : Finsupp.degree d1 + Finsupp.degree d2 = Finsupp.degree d := by
        rw [← map_add, hp]
      by_cases h1 : Finsupp.degree d1 = 0
      · have hd1 : d1 = 0 := (Finsupp.degree_eq_zero_iff d1).mp h1
        rw [hd1, hf a, zero_mul]
      · have h1pos : 0 < Finsupp.degree d1 := Nat.pos_of_ne_zero h1
        rw [ih f hf d2 (by omega), mul_zero]

/-- Two families of series whose coefficients agree in total degree `≤ 1` have
products whose coefficients agree in total degree equal to the number of factors. -/
lemma coeff_prod_eq_of_linear_agree
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ] :
    ∀ (s : Finset σ) (f g : σ → MvPowerSeries ι K),
      (∀ j, MvPowerSeries.coeff 0 (g j) = 0) →
      (∀ j (D : ι →₀ ℕ), Finsupp.degree D ≤ 1 →
        MvPowerSeries.coeff D (f j) = MvPowerSeries.coeff D (g j)) →
      ∀ e : ι →₀ ℕ, Finsupp.degree e = s.card →
        MvPowerSeries.coeff e (∏ j ∈ s, f j) = MvPowerSeries.coeff e (∏ j ∈ s, g j) := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro f g hg0 hfg e he
      simp only [Finset.card_empty] at he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he
      subst he0
      simp
  | cons a s ha ih =>
      intro f g hg0 hfg e he
      rw [Finset.card_cons ha] at he
      rw [Finset.prod_cons ha, Finset.prod_cons ha,
        MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨d1, d2⟩ := p
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : Finsupp.degree d1 + Finsupp.degree d2 = Finsupp.degree e := by
        rw [← map_add, hp]
      have hf0 : MvPowerSeries.coeff 0 (f a) = 0 := by
        rw [hfg a 0 (by simp), hg0 a]
      by_cases h1 : Finsupp.degree d1 = 0
      · have hd1 : d1 = 0 := (Finsupp.degree_eq_zero_iff d1).mp h1
        rw [hd1, hf0, hg0 a, zero_mul, zero_mul]
      · by_cases h2 : Finsupp.degree d1 = 1
        · have hd2 : Finsupp.degree d2 = s.card := by omega
          rw [ih f g hg0 hfg d2 hd2, hfg a d1 (by omega)]
        · have hd1two : 2 ≤ Finsupp.degree d1 := by omega
          have hd2 : Finsupp.degree d2 < s.card := by omega
          have hPf : MvPowerSeries.coeff d2 (∏ j ∈ s, f j) = 0 := by
            apply coeff_prod_eq_zero_of_lt_card s f ?_ d2 hd2
            intro j
            rw [hfg j 0 (by simp), hg0 j]
          have hPg : MvPowerSeries.coeff d2 (∏ j ∈ s, g j) = 0 := by
            apply coeff_prod_eq_zero_of_lt_card s g hg0 d2 hd2
          rw [hPf, hPg, mul_zero, mul_zero]

end ProdLinear

open ProdLinear in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ]
    (R : σ → MvPowerSeries ι K)
    (v : σ → ι)
    (hR : ∀ (j : σ) (d : ι → Nat), (∑ k : ι, d k) ≤ 1 →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R j) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X (v j)))
    (e : ι → Nat) (he : (∑ k : ι, e k) = Fintype.card σ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, R j) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, MvPowerSeries.X (v j)) := by
  classical
  have hdeg : Finsupp.degree (Finsupp.equivFunOnFinite.symm e) = Fintype.card σ := by
    rw [Finsupp.degree_eq_sum]
    have hfun : ∀ k : ι, (Finsupp.equivFunOnFinite.symm e) k = e k := by
      intro k
      exact congr_fun (Finsupp.coe_equivFunOnFinite_symm e) k
    simp only [hfun]
    exact he
  have hfg : ∀ (j : σ) (D : ι →₀ ℕ), Finsupp.degree D ≤ 1 →
      MvPowerSeries.coeff D (R j) = MvPowerSeries.coeff D (MvPowerSeries.X (v j)) := by
    intro j D hD
    have hsum : (∑ k : ι, D k) ≤ 1 := by
      rw [← Finsupp.degree_eq_sum]
      exact hD
    have hD' : Finsupp.equivFunOnFinite.symm (fun k => D k) = D := by
      ext k
      exact congr_fun (Finsupp.coe_equivFunOnFinite_symm (fun k => D k)) k
    rw [← hD']
    exact hR j (fun k => D k) hsum
  have hX0 : ∀ j : σ, MvPowerSeries.coeff 0 (MvPowerSeries.X (v j) : MvPowerSeries ι K) = 0 := by
    intro j
    simp
  have h := coeff_prod_eq_of_linear_agree (Finset.univ) R
    (fun j => MvPowerSeries.X (v j)) hX0 hfg (Finsupp.equivFunOnFinite.symm e) ?_
  · simpa using h
  · rw [hdeg, Finset.card_univ]
