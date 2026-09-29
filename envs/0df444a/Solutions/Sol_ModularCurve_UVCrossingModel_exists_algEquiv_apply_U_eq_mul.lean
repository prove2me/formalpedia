-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_algEquiv_apply_U_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bb931bf9-e974-5ac3-9622-fc3615b52f3c

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_exists_algEquiv_apply_X_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel MvPowerSeries

theorem solution
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] (π : Ô) (hπu : ¬ IsUnit π) (γ : (UVCrossingModel Ô π)ˣ) :
    ∃ τ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π,
      τ (U π) = (γ : UVCrossingModel Ô π) * U π ∧ τ (V π) = (↑γ⁻¹ : UVCrossingModel Ô π) * V π := by
  classical
  set I : Ideal (MvPowerSeries (Fin 2) Ô) := uvCrossingIdeal Ô π with hIdef
  set P : MvPowerSeries (Fin 2) Ô := X 0 * X 1 - C π with hP
  have hI : I = Ideal.span {P} := rfl

  obtain ⟨Γ, hΓ⟩ := mk_surjective π (γ : UVCrossingModel Ô π)
  obtain ⟨Γ', hΓ'⟩ := mk_surjective π (↑γ⁻¹ : UVCrossingModel Ô π)
  have hmk : ∀ F : MvPowerSeries (Fin 2) Ô, mk π F = Ideal.Quotient.mk I F := fun F => rfl
  have hprod : Γ * Γ' - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, ← hmk, ← hmk, map_mul, hΓ, hΓ', map_one, Units.mul_inv]
  obtain ⟨κ, hκ⟩ := Ideal.mem_span_singleton'.mp hprod

  have hc : constantCoeff Γ * constantCoeff Γ' = 1 - π * constantCoeff κ := by
    have h := congrArg constantCoeff hκ
    have h1 : constantCoeff (κ * P) = -(π * constantCoeff κ) := by
      rw [hP, map_mul, map_sub, map_mul, constantCoeff_X, zero_mul, constantCoeff_C, zero_sub, mul_neg, mul_comm]
    have h2 : constantCoeff (Γ * Γ' - 1) = constantCoeff Γ * constantCoeff Γ' - 1 := by
      rw [map_sub, map_mul, map_one]
    rw [h1, h2] at h
    linear_combination (-1 : Ô) * h
  have hunit : IsUnit (constantCoeff Γ * constantCoeff Γ') := by
    rw [hc]
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal π).mpr hπu)

  let f : Fin 2 → MvPowerSeries (Fin 2) Ô := ![Γ * X 0, Γ' * X 1]
  have hf0 : f 0 = Γ * X 0 := rfl
  have hf1 : f 1 = Γ' * X 1 := rfl
  have hcoeff : ∀ (G : MvPowerSeries (Fin 2) Ô) (i j : Fin 2),
      coeff (Finsupp.single j 1) (G * X i) = if i = j then constantCoeff G else 0 := by
    intro G i j
    rw [X_def, coeff_mul_monomial, mul_one]
    by_cases hij : i = j
    · subst hij; rw [if_pos le_rfl, if_pos rfl, tsub_self, coeff_zero_eq_constantCoeff_apply]
    · rw [if_neg, if_neg hij]
      intro hle
      have := hle i
      simp [Finsupp.single_apply, hij, Ne.symm hij] at this
  obtain ⟨e, he⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq f
    (by intro i; fin_cases i <;> simp [f, constantCoeff_X])
    (by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, hf0, hf1, hcoeff]
      simpa using hunit)
  have he0 : e (X 0) = Γ * X 0 := he 0
  have he1 : e (X 1) = Γ' * X 1 := he 1
  have heC : e (C π) = C π := by
    have := e.commutes π
    rwa [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

  have heP : e P = P * (1 + κ * (X 0 * X 1)) := by
    rw [hP, map_sub, map_mul, he0, he1, heC]
    have : Γ * X 0 * (Γ' * X 1) = (Γ * Γ') * (X 0 * X 1) := by ring
    rw [this, show Γ * Γ' = 1 + κ * (X 0 * X 1 - C π) by linear_combination (-1 : MvPowerSeries (Fin 2) Ô) * hκ]
    ring
  have hu : IsUnit (1 + κ * (X 0 * X 1) : MvPowerSeries (Fin 2) Ô) := by
    rw [isUnit_iff_constantCoeff]
    simp [constantCoeff_X]
  have hmap : I = I.map (e : MvPowerSeries (Fin 2) Ô →+* MvPowerSeries (Fin 2) Ô) := by
    rw [hI, Ideal.map_span, Set.image_singleton]
    show Ideal.span {P} = Ideal.span {e P}
    rw [heP, Ideal.span_singleton_mul_right_unit hu]
  refine ⟨Ideal.quotientEquivAlg I I e hmap, ?_, ?_⟩
  · show Ideal.Quotient.mk I (e (X 0)) = (γ : UVCrossingModel Ô π) * Ideal.Quotient.mk I (X 0)
    rw [he0, map_mul, ← hΓ]
    rfl
  · show Ideal.Quotient.mk I (e (X 1)) = (↑γ⁻¹ : UVCrossingModel Ô π) * Ideal.Quotient.mk I (X 1)
    rw [he1, map_mul, ← hΓ']
    rfl

end S_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_apply_U_eq_mul (solution)
