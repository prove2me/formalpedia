-- Prove2me | solution 1 for ModularCurve.qExpand_four_eisenstein4_mul_etaProd_identity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/05e472d9-1c5a-5988-b0f9-a8560eb20461

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularForm_sixteen_mul_E4_mul_eta_quarter_pow_eq
import Theorems.Thm_ModularCurve_hasSum_coeff_eisenstein4_qParam
import Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_four_eisenstein4_mul_etaProd_identity
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpand_four_eisenstein4_mul_etaProd_identity.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 etaProd ofPowerSeries_coeff_of_neg laurentMap_ofPowerSeries laurentMap_qExpand laurentMap_injective hasSum_coeff_eisenstein4_qParam hasSum_coeff_etaProd_pow hasSum_qParam_mul_laurent laurent_qParam_coeff_unique"
p2m_open "ModularCurve"
namespace JLTransfer4

open Complex
local notation "𝕢" => Function.Periodic.qParam

theorem four_pos' : (0 : ℝ) < 4 := by norm_num

def QS (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, HasSum (fun n : ℤ => A.coeff n * 𝕢 4 (τ : ℂ) ^ n) (F τ)

theorem QS.mul {A B : LaurentSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G) :
    QS (A * B) (fun τ => F τ * G τ) := fun τ =>
  ModularCurve.hasSum_qParam_mul_laurent 4 four_pos' A B F G hA hB τ

theorem QS.add {A B : LaurentSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G) :
    QS (A + B) (fun τ => F τ + G τ) := fun τ => by
  have h := (hA τ).add (hB τ)
  simpa only [HahnSeries.coeff_add, add_mul] using h

theorem QS.unique {A B : LaurentSeries ℂ} {F : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B F) : A = B :=
  ModularCurve.laurent_qParam_coeff_unique 4 four_pos' F A B hA hB

theorem hasSum_coeff_single (k : ℤ) (c q : ℂ) :
    HasSum (fun n : ℤ => (HahnSeries.single k c : LaurentSeries ℂ).coeff n * q ^ n) (c * q ^ k) := by
  have := hasSum_single (f := fun n : ℤ => (HahnSeries.single k c : LaurentSeries ℂ).coeff n * q ^ n) k
    (fun n hn => by simp only [HahnSeries.coeff_single_of_ne hn, zero_mul])
  simpa [HahnSeries.coeff_single_same] using this

theorem ofNat_eq_single (a : ℕ) [a.AtLeastTwo] :
    (OfNat.ofNat a : LaurentSeries ℂ) = HahnSeries.single (0 : ℤ) (OfNat.ofNat a : ℂ) := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) a, HahnSeries.C_apply]

theorem QS_ofNat (a : ℕ) [a.AtLeastTwo] : QS (OfNat.ofNat a : LaurentSeries ℂ) (fun _ => (OfNat.ofNat a : ℂ)) :=
  fun τ => by
  have h := hasSum_coeff_single 0 (OfNat.ofNat a : ℂ) (𝕢 4 (τ : ℂ))
  rw [zpow_zero, mul_one] at h
  rw [ofNat_eq_single]
  exact h

theorem hasSum_coeff_qExpand_ofPowerSeries (k : ℕ) [NeZero k] (G : PowerSeries ℤ) {q g : ℂ}
    (h : HasSum (fun m : ℕ => ((PowerSeries.coeff m G : ℤ) : ℂ) * (q ^ k) ^ m) g) :
    HasSum (fun n : ℤ =>
      (qExpand ℂ k (HahnSeries.ofPowerSeries ℤ ℂ (G.map (Int.castRingHom ℂ)))).coeff n * q ^ n) g := by
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne k
  let i : ℕ → ℤ := fun m => (k : ℤ) * m
  have hi : Function.Injective i := fun a b hab => by
    have := mul_left_cancel₀ hk0 hab
    exact_mod_cast this
  have hoff : ∀ n ∉ Set.range i,
      (qExpand ℂ k (HahnSeries.ofPowerSeries ℤ ℂ (G.map (Int.castRingHom ℂ)))).coeff n * q ^ n = 0 := by
    intro n hn
    by_cases hdvd : (k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hdvd
      rw [qExpand_coeff_mul]
      rcases le_or_gt 0 m with hm | hm
      · exfalso
        apply hn
        exact ⟨m.toNat, by simp [i, Int.toNat_of_nonneg hm]⟩
      · rw [ofPowerSeries_coeff_of_neg _ hm, zero_mul]
    · rw [qExpand_coeff_of_not_dvd k _ hdvd, zero_mul]
  refine (hi.hasSum_iff hoff).mp ?_
  convert h using 1
  funext m
  simp only [Function.comp_apply, i]
  rw [qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    show ((k : ℤ) * (m : ℤ)) = ((k * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
  rfl

theorem QS_qExpand_etaProd_pow (k : ℕ) [NeZero k] (a : ℕ) :
    QS (qExpand ℂ k (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ a))
      (fun τ => (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ k) ^ (n + 1))) ^ a) := fun τ => by
  have hq : ‖𝕢 4 (τ : ℂ) ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 4 τ) (NeZero.ne k)
  have h := hasSum_coeff_qExpand_ofPowerSeries k (etaProd ^ a) (ModularCurve.hasSum_coeff_etaProd_pow a hq)
  rwa [map_pow, map_pow] at h

theorem QS_etaProd_pow (a : ℕ) :
    QS (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ a)
      (fun τ => (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 1) ^ (n + 1))) ^ a) := fun τ => by
  have h := QS_qExpand_etaProd_pow 1 a τ
  rwa [qExpand_one_apply] at h

theorem qParam_one_eq_pow_four (τ : ℂ) : 𝕢 1 τ = 𝕢 4 τ ^ 4 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem qParam_one_half (τ : ℂ) : 𝕢 1 (τ / 2) = 𝕢 4 τ ^ 2 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem qParam_one_quarter (τ : ℂ) : 𝕢 1 (τ / 4) = 𝕢 4 τ ^ 1 := by
  rw [pow_one, Function.Periodic.qParam, Function.Periodic.qParam]; congr 1; push_cast; ring

theorem QS_qExpand_four_eisenstein4 :
    QS (qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (eisenstein4.map (Int.castRingHom ℂ))))
      (fun τ => ModularForm.E₄ τ) := fun τ => by
  apply hasSum_coeff_qExpand_ofPowerSeries
  have h := ModularCurve.hasSum_coeff_eisenstein4_qParam τ
  rwa [qParam_one_eq_pow_four] at h

theorem eta_eq (z : ℂ) : ModularForm.eta z = 𝕢 24 z * ∏' n : ℕ, (1 - 𝕢 1 z ^ (n + 1)) := rfl

theorem pref_0 (τ : ℂ) : 𝕢 24 (τ / 4) ^ 16 * 𝕢 24 (τ / 2) ^ 8 * 𝕢 24 τ ^ 16 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
theorem pref_1 (τ : ℂ) : 𝕢 24 (τ / 2) ^ 48 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem pref_2 (τ : ℂ) : 𝕢 24 (τ / 4) ^ 16 * 𝕢 24 (τ / 2) ^ 24 * 𝕢 24 τ ^ 8 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
theorem pref_3 (τ : ℂ) : 𝕢 24 (τ / 4) ^ 32 * 𝕢 24 τ ^ 16 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring

theorem euler_F2pp (τ : UpperHalfPlane) :
    16 * ModularForm.E₄ τ * (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 1) ^ (n + 1))) ^ 16 *
        (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16 =
      (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 48 +
        14 * (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 1) ^ (n + 1))) ^ 16 *
          (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 24 * (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 8 +
        (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 1) ^ (n + 1))) ^ 32 * (∏' n : ℕ, (1 - (𝕢 4 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16 := by
  have h := ModularForm.sixteen_mul_E4_mul_eta_quarter_pow_eq τ
  simp only [eta_eq, mul_pow, qParam_one_quarter (τ : ℂ), qParam_one_half (τ : ℂ), qParam_one_eq_pow_four (τ : ℂ)] at h
  have hc : 𝕢 1 (τ : ℂ) ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ hc
  linear_combination (exp := 1) h
    - 16 * ModularForm.E₄ τ * (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 1) ^ (n + 1))) ^ 16 *
        (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 2) ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 4) ^ (n + 1))) ^ 16 * pref_0 (τ : ℂ)
    + (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 2) ^ (n + 1))) ^ 48 * pref_1 (τ : ℂ)
    + 14 * (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 1) ^ (n + 1))) ^ 16 * (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 2) ^ (n + 1))) ^ 24 *
        (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 4) ^ (n + 1))) ^ 8 * pref_2 (τ : ℂ)
    + (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 1) ^ (n + 1))) ^ 32 * (∏' n : ℕ, (1 - (𝕢 4 (τ:ℂ) ^ 4) ^ (n + 1))) ^ 16 * pref_3 (τ : ℂ)

theorem F2pp_complex :
    16 * qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (eisenstein4.map (Int.castRingHom ℂ))) *
        HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16 *
        qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 8) *
        qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16) =
      qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 48) +
        14 * HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16 *
          qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 24) *
          qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 8) +
        HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 32 *
          qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16) := by
  have hA := ((((QS_ofNat 16).mul QS_qExpand_four_eisenstein4).mul (QS_etaProd_pow 16)).mul
    (QS_qExpand_etaProd_pow 2 8)).mul (QS_qExpand_etaProd_pow 4 16)
  have hB := ((QS_qExpand_etaProd_pow 2 48).add
    ((((QS_ofNat 14).mul (QS_etaProd_pow 16)).mul (QS_qExpand_etaProd_pow 2 24)).mul (QS_qExpand_etaProd_pow 4 8))).add
    ((QS_etaProd_pow 32).mul (QS_qExpand_etaProd_pow 4 16))
  refine hA.unique (fun τ => ?_)
  have h := hB τ
  beta_reduce
  rw [euler_F2pp τ]
  exact h

end JLTransfer4
end ModularCurve

end

set_option maxHeartbeats 1600000 in

theorem solution :
    16 * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ eisenstein4) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 *
        qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8) * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) =
      qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 48) +
        14 * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 * qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) *
          qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8) +
        HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 32 * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) := by
  apply ModularCurve.laurentMap_injective (f := Int.castRingHom ℂ) Int.cast_injective
  have h := ModularCurve.JLTransfer4.F2pp_complex
  simp only [map_add, map_mul, map_pow, map_ofNat, ModularCurve.laurentMap_qExpand, ModularCurve.laurentMap_ofPowerSeries] at h ⊢
  linear_combination h

end S_ModularCurve_qExpand_four_eisenstein4_mul_etaProd_identity
end P2MW
export P2MW.S_ModularCurve_qExpand_four_eisenstein4_mul_etaProd_identity (solution)
