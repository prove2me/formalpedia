-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.two_le_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2dce65a7-d845-5a8f-8993-a5d4341afa9d

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_two_le_ringKrullDim
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    2 ≤ ringKrullDim (UVCrossingModel W (π ^ E)) := by
  classical
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) W) := MvPowerSeries.isNoetherianRing_fin W 2
  set R := MvPowerSeries (Fin 2) W with hR
  set x : R := (MvPowerSeries.X 0 : R) * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E) with hx

  have hx0 : x ≠ 0 := by
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) h
    rw [hx, map_sub, map_zero, MvPowerSeries.coeff_C, if_neg (by
      intro h0
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h0
      simp at this), sub_zero] at h1
    rw [show (MvPowerSeries.X 0 : R) * MvPowerSeries.X 1 =
        MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 by
      rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul],
      MvPowerSeries.coeff_monomial_same] at h1
    exact one_ne_zero h1
  have hxreg : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx0

  have hxmax : x ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    rw [hx, map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
      MvPowerSeries.constantCoeff_C, zero_mul, zero_sub, IsUnit.neg_iff]
    intro hu
    exact hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π (by omega)) hu)
  have hdim : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hxreg hxmax
  have hR3 : ringKrullDim R = ((2 + 1 : ℕ) : WithBot ℕ∞) :=
    MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing W 2
  change 2 ≤ ringKrullDim (R ⧸ Ideal.span {x})
  rw [hR3] at hdim

  generalize ringKrullDim (R ⧸ Ideal.span {x}) = d at hdim
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hdim (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      have h5 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ⊤ := rfl
      have h6 : ((2 + 1 : ℕ) : WithBot ℕ∞) = (((2 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h4, h5, h6] at hdim
      exact ENat.top_ne_coe _ (WithBot.coe_injective hdim)
    | coe d =>
      have h' : ((d + 1 : ℕ) : WithBot ℕ∞) = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← hdim]; push_cast; rfl
      have h'' : d + 1 = 2 + 1 := by exact_mod_cast h'
      have : d = 2 := by omega
      subst this
      exact le_of_eq (by push_cast; rfl)

end S_ModularCurve_UVCrossingModel_two_le_ringKrullDim
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_two_le_ringKrullDim (solution)
