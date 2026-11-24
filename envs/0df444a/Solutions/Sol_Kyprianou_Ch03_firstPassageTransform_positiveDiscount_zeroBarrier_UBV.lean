-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier_UBV
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:04:03.71135+00:00
-- url     : https://prove2.me/submissions/79143e29-0f94-4e91-ac73-799c2fb6b3f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_ae_of_unboundedVariation

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Positive-discount zero-barrier Laplace transform under unbounded variation.
Splices the proved immediate-passage lemma `firstHittingIoi_zero_ae_of_unboundedVariation`
(same as the ACCEPTED zero-discount UBV leaf); only the a.e. congruence is adjusted
so that `finiteTime = 0` yields `exp(-q · 0) = 1` for `q > 0`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hUBV : ¬ L.BoundedVariation) :
    forall (q : Real), 0 < q ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), x = 0 ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  intro q _hq phi _hphi x hx finiteTime hfin
  subst hx
  -- `hNotDecreasing` is retained for source-exactness of the parent split; UBV
  -- immediate passage needs only `¬ L.BoundedVariation`.
  have _ := hNotDecreasing
  have hhit0 : ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 :=
    firstHittingIoi_zero_ae_of_unboundedVariation P F L hUBV
  have hae : (fun ω : Omega =>
      if firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = ⊤
      then (0 : ℝ)
      else Real.exp (-q * (finiteTime ω : ℝ))) =ᵐ[P] fun _ => (1 : ℝ) := by
    filter_upwards [hhit0] with ω hω
    have hne : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω ≠ ⊤ := by
      rw [hω]; exact WithTop.coe_ne_top
    have hbne : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω != ⊤ := by
      simpa [bne_iff_ne] using hne
    have hft : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω =
        (finiteTime ω : WithTop NNReal) := hfin ω hbne
    have hft0 : finiteTime ω = 0 := by
      have : (0 : WithTop NNReal) = (finiteTime ω : WithTop NNReal) := by rwa [hω] at hft
      exact WithTop.coe_injective this.symm
    simp [hne, hft0, Real.exp_zero]
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, Measure.real, measure_univ,
    ENNReal.toReal_one, mul_one]
  simp [Real.exp_zero]
