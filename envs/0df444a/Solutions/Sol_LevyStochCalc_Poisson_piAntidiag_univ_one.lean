-- Prove2me | solution 1 for LevyStochCalc.Poisson.piAntidiag_univ_one
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:42.37002+00:00
-- url     : https://prove2.me/submissions/46ef02ae-a3f8-4372-bea3-56d66a8b74f9

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degree-`s` chaos element of a profile on finitely many disjoint regions

For a Poisson random measure `N` with reference intensity `ν̂`, a finite family `B` of pairwise
disjoint regions of finite intensity `λ_k = ν̂(B k)` and a profile `c` constant on each region,
the degree-`s` element `D_s(c)` is the multinomial combination
`∑_(|α| = s) (s! / ∏_k α_k!) (∏_k c_k ^ α_k) ∏_k C_(α_k)(N(B k); λ_k)` of the products of Charlier
polynomials of the counts of the regions. It is a polynomial of degree `s` in those counts: the
degree-zero element is `1`, the degree-one element is `∑_k c_k Ñ(B k)`, and on a one-region
family the element is `c ^ s` times the degree-`s` Charlier element of the region.

The degree elements are square integrable, centred in positive degree and orthogonal across
degrees, with the Gram `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s` for the bilinear form
`⟨c, c'⟩ = ∑_k c_k c'_k λ_k`; on strips `(a, b] ×ˢ A k` the rates are `(b − a) ν(A k)`. The Gram
rests on the orthogonality of the products of Charlier polynomials across multi-degrees, with the
norming `∏_k α_k! λ_k ^ α_k`, and on the multinomial identity
`∑_(|α| = s) (s! / ∏ α_k!) ^ 2 (∏ α_k!) ∏ x_k ^ α_k = s! (∑ x_k) ^ s`. The degree-two element of
one profile is the quadratic element `markedSecondChaos` carried by that profile twice.

The bilinear form is degenerate on a region of zero intensity. The profile is constant on the
regions of one given family: no mode of `L²(ν)` beyond such combinations of indicators enters, and
no common refinement of two families is formed.

## Main definitions

* `LevyStochCalc.Poisson.markedChaosDegree` — the degree-`s` element of a profile on a finite
  family of regions.

## Main statements

* `LevyStochCalc.Poisson.sum_piAntidiag_multinomial_sq` — the multinomial identity behind the
  norming.
* `LevyStochCalc.Poisson.markedChaosDegree_one`, `LevyStochCalc.Poisson.markedChaosDegree_fin_one`
  — the degree-one element and the one-region case.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_mul` — the Gram
  `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s`.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_strip_mul` — the same on strips, at the rates
  `(b − a) ν(A k)`.
* `LevyStochCalc.Poisson.markedChaosDegree_two` — the degree-two element is the quadratic element
  of the profile.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The algebraic core -/

/-! ### The degree-`s` element of a mark profile -/



theorem _root_.solution (p : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin p)) 1
      = Finset.image (fun k : Fin p => Pi.single k 1) Finset.univ := by
  classical
  ext f
  simp only [Finset.mem_piAntidiag, Finset.mem_univ, not_true_eq_false, false_implies,
    implies_true, and_true, Finset.mem_image, true_and]
  constructor
  · intro hf
    have he : ∃ k : Fin p, f k ≠ 0 := by
      by_contra! h
      simpa [h] using hf
    obtain ⟨k, hk⟩ := he
    have hone : f k = 1 := by
      have hle : f k ≤ 1 := hf ▸ Finset.single_le_sum (fun j _ => Nat.zero_le (f j))
        (Finset.mem_univ k)
      omega
    refine ⟨k, ?_⟩
    funext j
    by_cases hj : j = k
    · subst j
      simp [hone]
    · rw [Pi.single_eq_of_ne hj]
      by_contra hne
      have hs : f j + f k ≤ ∑ i : Fin p, f i := by
        simpa [Finset.sum_pair hj] using
          (Finset.sum_le_sum_of_subset_of_nonneg (s := ({j,k} : Finset (Fin p)))
            (t := Finset.univ) (f := f) (Finset.subset_univ _) (fun i _ _ => Nat.zero_le (f i)))
      rw [hf, hone] at hs
      omega
  · rintro ⟨k, rfl⟩
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Pi.single, Function.update_of_ne hj]
    · simp
