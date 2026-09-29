-- Prove2me | solution 1 for ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fcaca323-c04f-5df3-96f5-4d1f8bc1a3f2

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Theorems.Thm_ModularCurve_c4_tatePowerSeries
import Theorems.Thm_ModularCurve_c6_tatePowerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex Function ModularForm CongruenceSubgroup ModularCurve HahnSeries IntermediateField
open scoped MatrixGroups ModularForm Manifold

namespace WeberCusp

section Forms

variable (M : ℕ) [NeZero M]

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ₁ᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

def E4Γ : ModularForm Γ₁ᴳ 4 := restrictForm (Subgroup.map_le_range _ _) E₄

def E6Γ : ModularForm Γ₁ᴳ 6 := restrictForm (Subgroup.map_le_range _ _) E₆

theorem isIntegralQExp_E4Γ : IsIntegralQExp (⇑(E4Γ M)) eisenstein4 := by
  rw [IsIntegralQExp, E4Γ, coe_restrictForm]
  exact ModularCurve.qExpansion_E4_eq_map_eisenstein4.symm

theorem isIntegralQExp_E6Γ : IsIntegralQExp (⇑(E6Γ M)) eisenstein6 := by
  rw [IsIntegralQExp, E6Γ, coe_restrictForm]
  exact ModularCurve.qExpansion_E6_eq_map_mk.symm

def E4mul (B : ModularForm Γ₁ᴳ 2) : ModularForm Γ₁ᴳ 6 := ((E4Γ M).mul B).mcast (by norm_num)

theorem isIntegralQExp_E4mul (B : ModularForm Γ₁ᴳ 2) (b : PowerSeries ℤ) (hb : IsIntegralQExp (⇑B) b) :
    IsIntegralQExp (⇑(E4mul M B)) (eisenstein4 * b) := by
  rw [IsIntegralQExp, E4mul, coe_mcast, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) (E4Γ M) B, map_mul,
    isIntegralQExp_E4Γ M, hb]

end Forms

section Series

variable (K : Type*) [Field K]

theorem c4_eq : (tateLaurent K).c₄ = intSeriesC K eisenstein4 := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, ModularCurve.c4_tatePowerSeries]
  rfl

theorem c6_eq : (tateLaurent K).c₆ = -intSeriesC K eisenstein6 := by
  rw [tateLaurent, WeierstrassCurve.map_c₆, ModularCurve.c6_tatePowerSeries, map_neg]
  rfl

theorem intSeriesC_ne_zero {p : PowerSeries ℤ} (h : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h0
  have h1 := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (p.map (Int.castRingHom K)) 0
  rw [intSeriesC] at h0
  rw [h0, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h, map_one] at h1
  simp at h1

theorem intSeriesC_eisenstein4_ne_zero : intSeriesC K eisenstein4 ≠ 0 :=
  intSeriesC_ne_zero K constantCoeff_eisenstein4

theorem intSeriesC_eisenstein6_ne_zero : intSeriesC K eisenstein6 ≠ 0 :=
  intSeriesC_ne_zero K constantCoeff_eisenstein6

variable {K} in
theorem C_mem (Γ : Subgroup SL(2, ℤ)) (x : K) : HahnSeries.C x ∈ qExpFunctionFieldC K Γ := by
  have h := IntermediateField.algebraMap_mem (qExpFunctionFieldC K Γ) x
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C] at h
  exact h

end Series

universe u in
theorem main (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈
        qExpFunctionFieldC K (Gamma1 M) := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : Fact (1 < M) := ⟨by omega⟩
  obtain ⟨B, D, b, d, hB, hD, -, hK⟩ :=
    ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum M
  obtain ⟨h2, h4⟩ := hK K ζ hζ 1 one_ne_zero
  simp only [one_mul, ZMod.val_one, pow_one] at h2 h4

  have hMK : (M : K) ≠ 0 := by
    haveI : NeZero (M : K) := IsPrimitiveRoot.neZero' hζ
    exact NeZero.ne (M : K)
  set F := qExpFunctionFieldC K (Gamma1 M) with hF
  set E4b : LaurentSeries K := intSeriesC K eisenstein4 with hE4b
  set E6b : LaurentSeries K := intSeriesC K eisenstein6 with hE6b
  have hE4 : E4b ≠ 0 := intSeriesC_eisenstein4_ne_zero K
  have hE6 : E6b ≠ 0 := intSeriesC_eisenstein6_ne_zero K

  have hC : ∀ k : ℕ, (M : LaurentSeries K) ^ k = HahnSeries.C ((M : K) ^ k) := by
    intro k; rw [map_pow, map_natCast]
  have inv3 : 1 + 12 * (toricPoint K 1 ζ).1 =
      HahnSeries.C (((M : K) ^ 3)⁻¹) * ∑ c : ZMod M, ζ ^ c.val • intSeriesC K (b c) := by
    rw [← h2, hC 3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero 3 hMK), map_one, one_mul]
  have inv5 : (toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄ =
      HahnSeries.C (((M : K) ^ 5)⁻¹) * ∑ c : ZMod M, ζ ^ c.val • intSeriesC K (d c) := by
    rw [← h4, hC 5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero 5 hMK), map_one, one_mul]
  refine ⟨?_, ?_⟩
  ·
    rw [c4_eq, c6_eq, inv3, div_neg, ← hE4b, ← hE6b]
    have e : E4b * (HahnSeries.C (((M : K) ^ 3)⁻¹) * ∑ c : ZMod M, ζ ^ c.val • intSeriesC K (b c)) / E6b =
        HahnSeries.C (((M : K) ^ 3)⁻¹) *
          ∑ c : ZMod M, HahnSeries.C (ζ ^ c.val) * (intSeriesC K (eisenstein4 * b c) / E6b) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [intSeriesC_mul, ← hE4b, ← HahnSeries.C_mul_eq_smul]
      field_simp
    rw [e]
    refine neg_mem (mul_mem (C_mem _ _) (sum_mem fun c _ => mul_mem (C_mem _ _) ?_))
    exact div_mem_qExpFunctionFieldC (E4mul M (B c)) (E6Γ M)
      (isIntegralQExp_E4mul M (B c) (b c) (hB c)) (isIntegralQExp_E6Γ M) hE6
  ·
    rw [c4_eq, inv5, ← hE4b]
    have e : HahnSeries.C (((M : K) ^ 5)⁻¹) * (∑ c : ZMod M, ζ ^ c.val • intSeriesC K (d c)) / E4b =
        HahnSeries.C (((M : K) ^ 5)⁻¹) *
          ∑ c : ZMod M, HahnSeries.C (ζ ^ c.val) * (intSeriesC K (d c) / E4b) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← HahnSeries.C_mul_eq_smul]
      ring
    rw [e]
    refine mul_mem (C_mem _ _) (sum_mem fun c _ => mul_mem (C_mem _ _) ?_)
    exact div_mem_qExpFunctionFieldC (D c) (E4Γ M) (hD c) (isIntegralQExp_E4Γ M) hE4

end WeberCusp

end

open ModularCurve WeierstrassCurve

universe u in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 ζ).1) / (tateLaurent K).c₆ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) ∧
      ((toricPoint K 1 ζ).1 + 6 * (toricPoint K 1 ζ).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄ ∈
        qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) :=
  WeberCusp.main K M hM ζ hζ

end S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
end P2MW
export P2MW.S_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1 (solution)
