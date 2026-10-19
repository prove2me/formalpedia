-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_injective_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:21:37.735737+00:00
-- url     : https://prove2.me/submissions/720d2b5c-aa16-4155-943c-89b14f94baf3

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_of_canonical_exponent
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_exponent_eq_sum_of_injective_coordinates

open scoped BigOperators

theorem solution
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (x0 : σ)
    (hv : Function.Injective v)
    (hdisj : ∀ i : Fin m, v i ≠ x0)
    (c : Fin m → ℂ) (e : Fin m → ℕ)
    (d : σ →₀ ℕ)
    (hbase : d x0 = 0)
    (hcoord : ∀ i : Fin m, d (v i) = e i)
    (hout : ∀ x : σ, x ≠ x0 → (∀ i : Fin m, v i ≠ x) → d x = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X (v i) + MvPowerSeries.C (c i)) ^ (e i)) = 1 := by
  have hd : d = ∑ i : Fin m, Finsupp.single (v i) (e i) :=
    OAI.PiExponent.AdmissibleFormalInterpolation.exponent_eq_sum_of_injective_coordinates
      v x0 hv hdisj e d hbase hcoord hout
  rw [hd]
  exact
    OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_canonical_exponent
      v c e