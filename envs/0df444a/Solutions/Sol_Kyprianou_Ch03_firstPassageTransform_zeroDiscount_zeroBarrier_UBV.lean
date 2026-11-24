-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_zeroDiscount_zeroBarrier_UBV
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:50:12.48788+00:00
-- url     : https://prove2.me/submissions/766a83a9-da97-4b2b-96db-8b630066560a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_ae_of_unboundedVariation

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hUBV : ¬ L.BoundedVariation) :
    forall (q : Real), q = 0 ->
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
  intro q hq phi _hphi x hx finiteTime _hfin
  subst hq
  subst hx
  -- `hNotDecreasing` is retained for source-exactness of the parent split; UBV
  -- immediate passage needs only `¬ L.BoundedVariation`.
  have _ := hNotDecreasing
  have hhit0 : ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 :=
    firstHittingIoi_zero_ae_of_unboundedVariation P F L hUBV
  have hae : (fun ω : Omega =>
      if firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = ⊤
      then (0 : ℝ)
      else Real.exp (-(0 : ℝ) * (finiteTime ω : ℝ))) =ᵐ[P] fun _ => (1 : ℝ) := by
    filter_upwards [hhit0] with ω hω
    have hne : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω ≠ ⊤ := by
      rw [hω]; exact WithTop.coe_ne_top
    simp [hne]
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, Measure.real, measure_univ,
    ENNReal.toReal_one, mul_one]
  simp
