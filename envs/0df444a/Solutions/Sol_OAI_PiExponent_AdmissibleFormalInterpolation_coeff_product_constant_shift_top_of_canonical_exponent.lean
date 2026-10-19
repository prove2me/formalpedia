-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_canonical_exponent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:27:05.715889+00:00
-- url     : https://prove2.me/submissions/a78c1e72-fa26-4df0-8a8e-e619c41e3f54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_support_top
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_prod_eq_one_of_support_bounds

open scoped BigOperators

theorem solution
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (c : Fin m → ℂ) (e : Fin m → ℕ) :
    MvPowerSeries.coeff (∑ i : Fin m, Finsupp.single (v i) (e i))
        (∏ i : Fin m,
          (MvPowerSeries.X (v i) + MvPowerSeries.C (c i)) ^ (e i)) = 1 := by
  classical
  apply OAI.PiExponent.AdmissibleFormalInterpolation.coeff_prod_eq_one_of_support_bounds
      (s := Finset.univ)
      (f := fun i => (MvPowerSeries.X (v i) + MvPowerSeries.C (c i)) ^ (e i))
      (d := fun i => Finsupp.single (v i) (e i))
  · intro i hi k hk
    exact (OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support_top
      (v i) (c i) (e i)).2 k hk
  · intro i hi
    exact (OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support_top
      (v i) (c i) (e i)).1