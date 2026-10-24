-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_integrand_nonnegative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:46:14.071205+00:00
-- url     : https://prove2.me/submissions/8b412e83-f419-46cb-b20c-448369ffc32e

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) (hT : 0 < T) :
    (0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)]
        (fun t : Real => (T - t) ^ n / (n.factorial : Real))) ∧
      MeasureTheory.Integrable
        (fun t : Real => (T - t) ^ n / (n.factorial : Real))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)) := by
  let f : Real → Real := fun t => (T - t) ^ n / (n.factorial : Real)
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2.le
    have hden : 0 < (n.factorial : Real) := by
      exact_mod_cast Nat.factorial_pos n
    exact div_nonneg (pow_nonneg hnonneg n) (le_of_lt hden)
  · have hbase : Continuous (fun t : Real => T - t) :=
      continuous_const.sub continuous_id
    have hf : Continuous f := by
      dsimp [f]
      exact hbase.pow n |>.div_const _
    have hIcc : MeasureTheory.IntegrableOn f (Set.Icc (0 : Real) T)
        MeasureTheory.volume := hf.integrableOn_Icc
    exact hIcc.mono_set Set.Ioo_subset_Icc_self |>.integrable