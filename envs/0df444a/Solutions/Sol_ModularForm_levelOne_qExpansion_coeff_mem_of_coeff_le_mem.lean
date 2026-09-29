-- Prove2me | solution 1 for ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e175d16b-0264-5384-9bf3-7511d2939bf1

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem

open UpperHalfPlane
open scoped MatrixGroups

namespace A2LevelOneCrit

noncomputable def cInt (N i : ℕ) : PowerSeries ℤ :=
  ModularCurve.eisenstein4 ^ (3 * i) * ModularCurve.dedekindEtaUnit ^ (N - i)

theorem constantCoeff_eisenstein4 :
    PowerSeries.constantCoeff ModularCurve.eisenstein4 = 1 := by
  rw [ModularCurve.eisenstein4, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_mk]
  simp

theorem constantCoeff_cInt (N i : ℕ) : PowerSeries.constantCoeff (cInt N i) = 1 := by
  rw [cInt, map_mul, map_pow, map_pow, constantCoeff_eisenstein4,
    ModularCurve.constantCoeff_dedekindEtaUnit, one_pow, one_pow, one_mul]

noncomputable def B (N i : ℕ) : PowerSeries ℂ :=
  (PowerSeries.X ^ (N - i) * cInt N i).map (Int.castRingHom ℂ)

theorem B_eq (N i : ℕ) :
    B N i = (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ (3 * i) *
      (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ (N - i) := by
  have h4 : qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) =
      PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 :=
    ModularCurve.qExpansion_E4_eq_map_eisenstein4
  rw [h4, ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, B, cInt]
  simp only [map_mul, map_pow, mul_pow]
  ring

theorem coeff_B (N i m : ℕ) :
    (B N i).coeff m =
      if N - i ≤ m then (((cInt N i).coeff (m - (N - i)) : ℤ) : ℂ) else 0 := by
  rw [B, PowerSeries.coeff_map, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem coeff_B_eq_intCast (N i m : ℕ) : ∃ z : ℤ, (B N i).coeff m = (z : ℂ) := by
  rw [coeff_B]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

theorem coeff_B_self (N i : ℕ) : (B N i).coeff (N - i) = 1 := by
  rw [coeff_B, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_cInt, Int.cast_one]

theorem coeff_B_of_lt {N i m : ℕ} (h : m < N - i) : (B N i).coeff m = 0 := by
  rw [coeff_B, if_neg (not_le.mpr h)]

theorem coeff_B_mem (R : Subring ℂ) (N i m : ℕ) : (B N i).coeff m ∈ R := by
  obtain ⟨z, hz⟩ := coeff_B_eq_intCast N i m
  rw [hz]
  exact intCast_mem R z

theorem ofPowerSeries_qExpansion_discriminant_ne_zero :
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  have h0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    exact h
  have h1 := ModularForm.discriminant_qExpansion_coeff_one
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem qExpansion_eq_sum (N : ℕ) (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧
      qExpansion 1 (F : ℍ → ℂ) =
        ∑ i ∈ Finset.range (N + 1), PowerSeries.C (P.coeff i) * B N i := by
  obtain ⟨P, hdeg, hP⟩ := ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne N F
  refine ⟨P, hdeg, ?_⟩
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)

  set A : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) :
    LaurentSeries ℂ) with hA
  set D : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
    LaurentSeries ℂ) with hD
  have hD0 : D ≠ 0 := ofPowerSeries_qExpansion_discriminant_ne_zero
  change HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (F : ℍ → ℂ)) = _
  rw [hP, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsplit : D ^ N = D ^ i * D ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hiN]
  have hDi : D ^ i ≠ 0 := pow_ne_zero _ hD0
  have hJ : (A ^ 3 / D) ^ i * D ^ N = A ^ (3 * i) * D ^ (N - i) := by
    rw [div_pow, hsplit, ← pow_mul, div_mul_eq_mul_div, mul_comm (D ^ i) (D ^ (N - i)),
      ← mul_assoc, mul_div_assoc, div_self hDi, mul_one]
  rw [Algebra.smul_def, mul_assoc, hJ, map_mul, B_eq, map_mul, map_pow, map_pow]
  congr 1

theorem coeff_sum_C_mul_B (N : ℕ) (P : Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ Finset.range (N + 1), PowerSeries.C (P.coeff i) * B N i).coeff m =
      ∑ i ∈ Finset.range (N + 1), P.coeff i * (B N i).coeff m := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_C_mul]

theorem coeff_mem_of_le (N : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ N) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (∑ i ∈ Finset.range (N + 1), P.coeff i * (B N i).coeff n) ∈ R) :
    ∀ i, P.coeff i ∈ R := by

  have key : ∀ j, j ≤ N → P.coeff (N - j) ∈ R := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hmem : N - j ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le N j))
      have hsum := hF j hj
      rw [← Finset.add_sum_erase _ _ hmem] at hsum
      have hself : (B N (N - j)).coeff j = 1 := by
        have h := coeff_B_self N (N - j)
        rwa [Nat.sub_sub_self hj] at h
      rw [hself, mul_one] at hsum

      have hrest : (∑ i ∈ (Finset.range (N + 1)).erase (N - j),
          P.coeff i * (B N i).coeff j) ∈ R := by
        refine Subring.sum_mem R fun i hi => ?_
        have hi' := Finset.mem_erase.mp hi
        have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi'.2)
        rcases lt_or_gt_of_ne hi'.1 with hlt | hgt
        ·
          have hj' : j < N - i := by omega
          rw [coeff_B_of_lt hj', mul_zero]
          exact zero_mem R
        ·
          have hcoeff : P.coeff i ∈ R := by
            have h1 : N - i < j := by omega
            have h2 := ih (N - i) h1 (Nat.sub_le N i)
            rwa [Nat.sub_sub_self hiN] at h2
          exact mul_mem hcoeff (coeff_B_mem R N i j)
      have : P.coeff (N - j) =
          (P.coeff (N - j) + ∑ i ∈ (Finset.range (N + 1)).erase (N - j),
            P.coeff i * (B N i).coeff j) -
          ∑ i ∈ (Finset.range (N + 1)).erase (N - j), P.coeff i * (B N i).coeff j := by ring
      rw [this]
      exact sub_mem hsum hrest
  intro i
  rcases le_or_gt i N with hi | hi
  · have := key (N - i) (Nat.sub_le N i)
    rwa [Nat.sub_sub_self hi] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hi)]
    exact zero_mem R

theorem main (N : ℕ) (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (qExpansion 1 (F : ℍ → ℂ)).coeff n ∈ R) (n : ℕ) :
    (qExpansion 1 (F : ℍ → ℂ)).coeff n ∈ R := by
  obtain ⟨P, hdeg, hP⟩ := qExpansion_eq_sum N F
  have hF' : ∀ m ≤ N, (∑ i ∈ Finset.range (N + 1), P.coeff i * (B N i).coeff m) ∈ R := by
    intro m hm
    rw [← coeff_sum_C_mul_B, ← hP]
    exact hF m hm
  have hcoeff := coeff_mem_of_le N P hdeg R hF'
  rw [hP, coeff_sum_C_mul_B]
  exact Subring.sum_mem R fun i _ => mul_mem (hcoeff i) (coeff_B_mem R N i n)

end A2LevelOneCrit

set_option autoImplicit false
open scoped MatrixGroups in
theorem solution (N : ℕ)
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R :=
  A2LevelOneCrit.main N F R hF n

end S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem
end P2MW
export P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem (solution)
