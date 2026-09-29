-- Prove2me | solution 1 for ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/260e0a81-0bfd-5688-abaa-a1c0ffd002f3

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open ModularCurve

namespace CONVgen

variable {Γ : Subgroup SL(2, ℤ)}

local notation "GG" Γ => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem isIntegralQExp_mul (hΓ : (1 : ℝ) ∈ (GG Γ).strictPeriods) {k₁ k₂ : ℤ}
    (f₁ : ModularForm (GG Γ) k₁) (f₂ : ModularForm (GG Γ) k₂) {p₁ p₂ : PowerSeries ℤ}
    (h₁ : IsIntegralQExp f₁ p₁) (h₂ : IsIntegralQExp f₂ p₂) : IsIntegralQExp ⇑(f₁.mul f₂) (p₁ * p₂) := by
  unfold IsIntegralQExp at *
  rw [ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos hΓ f₁ f₂, map_mul, h₁, h₂]

theorem isIntegralQExp_mcast {a b : ℤ} (h : a = b) (f : ModularForm (GG Γ) a) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) : IsIntegralQExp ⇑(ModularForm.mcast h f) p := hf

theorem isIntegralQExp_pow (hΓ : (1 : ℝ) ∈ (GG Γ).strictPeriods) {k : ℤ} (f : ModularForm (GG Γ) k) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) : ∀ n : ℕ, IsIntegralQExp ⇑(f.pow n) (p ^ n)
  | 0 => by rw [ModularForm.coe_pow, pow_zero, pow_zero]; exact isIntegralQExp_one
  | n + 1 => by
      have ih := isIntegralQExp_pow hΓ f hf n
      unfold IsIntegralQExp at *
      rw [ModularForm.coe_pow, pow_succ (⇑f : UpperHalfPlane → ℂ) n, ← ModularForm.coe_pow,
        ModularForm.qExpansion_mul_coe one_pos hΓ (f.pow n) f, pow_succ, map_mul, ih, hf]

end CONVgen

namespace CONVgen

theorem intSeriesC_pow (K : Type*) [Field K] (p : PowerSeries ℤ) : ∀ n : ℕ, intSeriesC K (p ^ n) = intSeriesC K p ^ n
  | 0 => by rw [pow_zero, pow_zero, intSeriesC_one]
  | n + 1 => by rw [pow_succ, pow_succ, intSeriesC_mul, intSeriesC_pow K p n]

theorem intSeriesC_X (K : Type*) [Field K] : intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
  unfold intSeriesC; rw [PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

end CONVgen

open CONVgen in
theorem solution
    (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (r : LaurentSeries K) (hr : r ∈ ModularCurve.intFormRatiosC K Γ) :
    ∃ (a b : LaurentSeries K) (m n : ℤ) (P Q : PowerSeries ℤ),
      a ∈ ModularCurve.qExpFunctionFieldC K Γ ∧ b ∈ ModularCurve.qExpFunctionFieldC K Γ ∧
      a = HahnSeries.single m 1 * ModularCurve.intSeriesC K P ∧
      b = HahnSeries.single n 1 * ModularCurve.intSeriesC K Q ∧
      b ≠ 0 ∧ r * b = a := by
  classical
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr

  have hle : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  let Δ : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    restrictForm hle (ModularFormClass.modularForm CuspForm.discriminant)
  set u : PowerSeries ℤ := dedekindEtaUnit with hu
  set uinv : PowerSeries ℤ := dedekindEtaUnitInv with huinv
  have huu : u * uinv = 1 := dedekindEtaUnit_mul_inv
  have hΔ : IsIntegralQExp ⇑Δ (PowerSeries.X * u) := by
    show PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * dedekindEtaUnit) = UpperHalfPlane.qExpansion 1 ModularForm.discriminant
    exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

  set U := intSeriesC K u with hU
  set Uinv := intSeriesC K uinv with hUinv
  have hUU : U * Uinv = 1 := by rw [hU, hUinv, ← intSeriesC_mul, huu, intSeriesC_one]
  have hU0 : U ≠ 0 := left_ne_zero_of_mul_eq_one hUU
  have hXu : ∀ n : ℕ, intSeriesC K ((PowerSeries.X * u) ^ n) = HahnSeries.single (n : ℤ) 1 * U ^ n := by
    intro n
    rw [intSeriesC_pow, intSeriesC_mul, intSeriesC_X, mul_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hXu0 : ∀ n : ℕ, intSeriesC K ((PowerSeries.X * u) ^ n) ≠ 0 := by
    intro n; rw [hXu]
    exact mul_ne_zero (by rw [Ne, HahnSeries.single_eq_zero_iff]; exact one_ne_zero) (pow_ne_zero _ hU0)
  have hXuinv : ∀ n : ℕ, (intSeriesC K ((PowerSeries.X * u) ^ n))⁻¹ = HahnSeries.single (-(n : ℤ)) 1 * Uinv ^ n := by
    intro n
    rw [hXu]
    apply inv_eq_of_mul_eq_one_right
    calc HahnSeries.single (n : ℤ) (1 : K) * U ^ n * (HahnSeries.single (-(n : ℤ)) 1 * Uinv ^ n)
        = (HahnSeries.single (n : ℤ) (1 : K) * HahnSeries.single (-(n : ℤ)) 1) * (U * Uinv) ^ n := by rw [mul_pow]; ring
      _ = 1 := by rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one, hUU, one_pow, mul_one]
  have hUinv_pow : ∀ n : ℕ, Uinv ^ n = intSeriesC K (uinv ^ n) := fun n => by rw [hUinv, intSeriesC_pow]

  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  ·
    let num : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (12 * (n : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (f.mul (g.pow 11))
    let numb : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (12 * (n : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) ((g.pow 11).mul g)
    let den : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (12 * (n : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (Δ.pow n)
    have hnum : IsIntegralQExp ⇑num (pf * pg ^ 11) := isIntegralQExp_mcast _ _ (isIntegralQExp_mul hΓ f _ hf (isIntegralQExp_pow hΓ g hg 11))
    have hnumb : IsIntegralQExp ⇑numb (pg ^ 11 * pg) := isIntegralQExp_mcast _ _ (isIntegralQExp_mul hΓ _ g (isIntegralQExp_pow hΓ g hg 11) hg)
    have hden : IsIntegralQExp ⇑den ((PowerSeries.X * u) ^ n) := isIntegralQExp_mcast _ _ (isIntegralQExp_pow hΓ Δ hΔ n)
    refine ⟨intSeriesC K (pf * pg ^ 11) / intSeriesC K ((PowerSeries.X * u) ^ n), intSeriesC K (pg ^ 11 * pg) / intSeriesC K ((PowerSeries.X * u) ^ n),
      -(n : ℤ), -(n : ℤ), pf * pg ^ 11 * uinv ^ n, pg ^ 11 * pg * uinv ^ n,
      div_mem_qExpFunctionFieldC num den hnum hden (hXu0 n), div_mem_qExpFunctionFieldC numb den hnumb hden (hXu0 n), ?_, ?_, ?_, ?_⟩
    · rw [div_eq_mul_inv, hXuinv, intSeriesC_mul K (pf * pg ^ 11) (uinv ^ n), ← hUinv_pow]; ring
    · rw [div_eq_mul_inv, hXuinv, intSeriesC_mul K (pg ^ 11 * pg) (uinv ^ n), ← hUinv_pow]; ring
    · refine div_ne_zero ?_ (hXu0 n)
      rw [intSeriesC_mul, intSeriesC_pow]; exact mul_ne_zero (pow_ne_zero _ hg0) hg0
    · rw [intSeriesC_mul K pf (pg ^ 11), intSeriesC_mul K (pg ^ 11) pg, div_mul_div_comm,
        mul_comm (intSeriesC K (pg ^ 11)) (intSeriesC K pg), ← mul_assoc, mul_comm (intSeriesC K pf) (intSeriesC K pg), mul_assoc,
        mul_div_mul_left _ _ hg0]
  ·
    let num : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0 :=
      ModularForm.mcast (by push_cast; ring) ((f.mul (g.pow 11)).mul (Δ.pow n))
    let numb : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0 :=
      ModularForm.mcast (by push_cast; ring) (((g.pow 11).mul g).mul (Δ.pow n))
    have hnum : IsIntegralQExp ⇑num (pf * pg ^ 11 * (PowerSeries.X * u) ^ n) :=
      isIntegralQExp_mcast _ _ (isIntegralQExp_mul hΓ _ _ (isIntegralQExp_mul hΓ f _ hf (isIntegralQExp_pow hΓ g hg 11)) (isIntegralQExp_pow hΓ Δ hΔ n))
    have hnumb : IsIntegralQExp ⇑numb (pg ^ 11 * pg * (PowerSeries.X * u) ^ n) :=
      isIntegralQExp_mcast _ _ (isIntegralQExp_mul hΓ _ _ (isIntegralQExp_mul hΓ _ g (isIntegralQExp_pow hΓ g hg 11) hg) (isIntegralQExp_pow hΓ Δ hΔ n))
    have hone : IsIntegralQExp ⇑(1 : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) 1 := by
      rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
    have h10 : intSeriesC K 1 ≠ 0 := by rw [intSeriesC_one]; exact one_ne_zero
    refine ⟨intSeriesC K (pf * pg ^ 11 * (PowerSeries.X * u) ^ n) / intSeriesC K 1, intSeriesC K (pg ^ 11 * pg * (PowerSeries.X * u) ^ n) / intSeriesC K 1,
      0, 0, pf * pg ^ 11 * (PowerSeries.X * u) ^ n, pg ^ 11 * pg * (PowerSeries.X * u) ^ n,
      div_mem_qExpFunctionFieldC num 1 hnum hone h10, div_mem_qExpFunctionFieldC numb 1 hnumb hone h10, ?_, ?_, ?_, ?_⟩
    · rw [intSeriesC_one, div_one, HahnSeries.single_zero_one, one_mul]
    · rw [intSeriesC_one, div_one, HahnSeries.single_zero_one, one_mul]
    · rw [intSeriesC_one, div_one, intSeriesC_mul K (pg ^ 11 * pg), intSeriesC_mul K (pg ^ 11) pg, intSeriesC_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg0) hg0) (hXu0 n)
    · rw [intSeriesC_one, div_one, div_one, intSeriesC_mul K (pg ^ 11 * pg), intSeriesC_mul K (pg ^ 11) pg, intSeriesC_mul K (pf * pg ^ 11),
        intSeriesC_mul K pf (pg ^ 11), div_mul_eq_mul_div]

      rw [mul_assoc (intSeriesC K (pg ^ 11)) (intSeriesC K pg), mul_comm (intSeriesC K pg), ← mul_assoc, ← mul_assoc, mul_div_cancel_right₀ _ hg0]

end S_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
end P2MW
export P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC (solution)
