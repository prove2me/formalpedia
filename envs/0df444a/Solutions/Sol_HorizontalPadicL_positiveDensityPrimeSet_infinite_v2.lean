-- Prove2me | solution 1 for HorizontalPadicL.positiveDensityPrimeSet_infinite_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T10:57:05.300059+00:00
-- url     : https://prove2.me/submissions/104adf3a-fac6-44bd-9842-511cbe936e77

import Definitions.Def_KN_HorizontalPadicLAux
import Mathlib.Algebra.Order.Archimedean.IndicatorCard

set_option autoImplicit false

open Filter
open HorizontalPadicL

theorem solution
    (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity A δ) : A.Infinite := by
  classical
  by_contra hA
  have hAfin : A.Finite := not_not.mp hA
  let P : Set ℕ := {ℓ | ℓ.Prime ∧ ℓ ∈ A}
  let num : ℕ → ℕ := fun X => ((Finset.range X).filter fun ℓ => ℓ ∈ P).card
  let den : ℕ → ℕ := fun X => ((Finset.range X).filter Nat.Prime).card
  have hPfin : P.Finite := hAfin.subset (by
    intro ℓ hℓ
    exact hℓ.2)
  have hnum_eventually :
      ∀ᶠ X in atTop, num X = Nat.card P := by
    simpa [num, Finset.card_filter, Set.indicator] using
      (Set.sum_indicator_eventually_eq_card (α := ℕ) 1 hPfin)
  have hden_nat : Tendsto den atTop atTop := by
    have h :=
      (Set.infinite_iff_tendsto_sum_indicator_atTop
        (R := ℕ) (r := 1) Nat.zero_lt_one).mp Nat.infinite_setOfPred_prime
    simpa only [den, Finset.card_filter, Set.indicator_apply, Set.mem_ofPred_eq,
      Pi.one_apply] using h
  have hden_real : Tendsto (fun X => (den X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hden_nat
  have hnum_real :
      Tendsto (fun X => (num X : ℝ)) atTop (nhds (Nat.card P : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hnum_eventually] with X hX
    simp [hX]
  have hzero : Tendsto (fun X => (num X : ℝ) / (den X : ℝ))
      atTop (nhds 0) := hnum_real.div_atTop hden_real
  have hdensity' : Tendsto (fun X => (num X : ℝ) / (den X : ℝ))
      atTop (nhds δ) := by
    simpa [HasPrimeNaturalDensity, num, den, P] using hdensity
  have hδzero : δ = 0 := tendsto_nhds_unique hdensity' hzero
  exact (ne_of_gt hδ) hδzero
