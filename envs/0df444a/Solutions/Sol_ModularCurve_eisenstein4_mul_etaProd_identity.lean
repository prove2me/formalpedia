-- Prove2me | solution 1 for ModularCurve.eisenstein4_mul_etaProd_identity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3dd08490-979a-53aa-b1fc-ac9223d3ee46

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularForm_E4_mul_etaProduct_eq
import Theorems.Thm_ModularCurve_hasSum_coeff_eisenstein4_qParam
import Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisenstein4_mul_etaProd_identity
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_eisenstein4_mul_etaProd_identity.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 etaProd ofPowerSeries_coeff_of_neg laurentMap_single laurentMap_ofPowerSeries laurentMap_qExpand laurentMap_injective hasSum_coeff_eisenstein4_qParam hasSum_coeff_etaProd_pow hasSum_qParam_mul_laurent laurent_qParam_coeff_unique"
p2m_open "ModularCurve"
namespace JMTransfer

open Complex
local notation "𝕢" => Function.Periodic.qParam

def QS (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, HasSum (fun n : ℤ => A.coeff n * 𝕢 1 (τ : ℂ) ^ n) (F τ)

theorem QS.mul {A B : LaurentSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G) :
    QS (A * B) (fun τ => F τ * G τ) := fun τ =>
  ModularCurve.hasSum_qParam_mul_laurent 1 one_pos A B F G hA hB τ

theorem QS.add {A B : LaurentSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G) :
    QS (A + B) (fun τ => F τ + G τ) := fun τ => by
  have h := (hA τ).add (hB τ)
  simpa only [HahnSeries.coeff_add, add_mul] using h

theorem QS.unique {A B : LaurentSeries ℂ} {F : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B F) : A = B :=
  ModularCurve.laurent_qParam_coeff_unique 1 one_pos F A B hA hB

theorem hasSum_coeff_single (k : ℤ) (c q : ℂ) :
    HasSum (fun n : ℤ => (HahnSeries.single k c : LaurentSeries ℂ).coeff n * q ^ n) (c * q ^ k) := by
  have := hasSum_single (f := fun n : ℤ => (HahnSeries.single k c : LaurentSeries ℂ).coeff n * q ^ n) k
    (fun n hn => by simp only [HahnSeries.coeff_single_of_ne hn, zero_mul])
  simpa [HahnSeries.coeff_single_same] using this

theorem QS_single_one : QS (HahnSeries.single (1 : ℤ) (1 : ℂ)) (fun τ => 𝕢 1 (τ : ℂ)) := fun τ => by
  simpa using hasSum_coeff_single 1 1 (𝕢 1 (τ : ℂ))

theorem QS_single_two : QS (HahnSeries.single (2 : ℤ) (1 : ℂ)) (fun τ => 𝕢 1 (τ : ℂ) ^ 2) := fun τ => by
  simpa using hasSum_coeff_single 2 1 (𝕢 1 (τ : ℂ))

theorem ofNat_eq_single (a : ℕ) [a.AtLeastTwo] :
    (OfNat.ofNat a : LaurentSeries ℂ) = HahnSeries.single (0 : ℤ) (OfNat.ofNat a : ℂ) := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) a, HahnSeries.C_apply]

theorem QS_ofNat (a : ℕ) [a.AtLeastTwo] : QS (OfNat.ofNat a : LaurentSeries ℂ) (fun _ => (OfNat.ofNat a : ℂ)) :=
  fun τ => by
  have h := hasSum_coeff_single 0 (OfNat.ofNat a : ℂ) (𝕢 1 (τ : ℂ))
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
      (fun τ => (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ k) ^ (n + 1))) ^ a) := fun τ => by
  have hq : ‖𝕢 1 (τ : ℂ) ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ) (NeZero.ne k)
  have h := hasSum_coeff_qExpand_ofPowerSeries k (etaProd ^ a) (ModularCurve.hasSum_coeff_etaProd_pow a hq)
  rwa [map_pow, map_pow] at h

theorem QS_etaProd_pow (a : ℕ) :
    QS (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ a)
      (fun τ => (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ a) := fun τ => by
  have h := QS_qExpand_etaProd_pow 1 a τ
  rw [qExpand_one_apply] at h
  simpa only [pow_one] using h

theorem QS_eisenstein4 :
    QS (HahnSeries.ofPowerSeries ℤ ℂ (eisenstein4.map (Int.castRingHom ℂ))) (fun τ => ModularForm.E₄ τ) := fun τ => by
  have h := ModularCurve.hasSum_coeff_eisenstein4_qParam τ
  have h' : HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * (𝕢 1 (τ : ℂ) ^ 1) ^ m)
      (ModularForm.E₄ τ) := by simpa only [pow_one] using h
  have h2 := hasSum_coeff_qExpand_ofPowerSeries 1 eisenstein4 h'
  rwa [qExpand_one_apply] at h2

theorem eta_eq (z : ℂ) : ModularForm.eta z = 𝕢 24 z * ∏' n : ℕ, (1 - 𝕢 1 z ^ (n + 1)) := rfl

theorem qParam_two_mul (z : ℂ) : 𝕢 1 (2 * z) = 𝕢 1 z ^ 2 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem qParam_four_mul (z : ℂ) : 𝕢 1 (4 * z) = 𝕢 1 z ^ 4 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring

theorem pref_L (z : ℂ) : 𝕢 1 z ^ 4 = 𝕢 24 z ^ 16 * 𝕢 24 (2 * z) ^ 8 * 𝕢 24 (4 * z) ^ 16 := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
theorem pref_a (z : ℂ) : 𝕢 24 (2 * z) ^ 48 = 𝕢 1 z ^ 4 := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem pref_b (z : ℂ) : 𝕢 24 z ^ 8 * 𝕢 24 (2 * z) ^ 24 * 𝕢 24 (4 * z) ^ 16 = 𝕢 1 z ^ 5 := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
theorem pref_c (z : ℂ) : 𝕢 24 z ^ 16 * 𝕢 24 (4 * z) ^ 32 = 𝕢 1 z ^ 6 := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring

theorem euler_F2p (τ : UpperHalfPlane) :
    ModularForm.E₄ τ * (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 16 *
        (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16 =
      (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 48 +
        224 * 𝕢 1 (τ : ℂ) * (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 8 *
          (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 24 * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16 +
        256 * 𝕢 1 (τ : ℂ) ^ 2 * (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 16 *
          (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 32 := by
  have h := ModularForm.E4_mul_etaProduct_eq τ
  simp only [eta_eq, mul_pow, qParam_two_mul (τ : ℂ), qParam_four_mul (τ : ℂ)] at h
  have hc : 𝕢 1 (τ : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ (exp_ne_zero _)
  apply mul_left_cancel₀ hc
  linear_combination (exp := 1) h
    + ModularForm.E₄ τ * ((∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 16 *
        (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16)
        * pref_L (τ : ℂ)
    + (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 48 * pref_a (τ : ℂ)
    + 224 * ((∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 8 * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 24
        * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 16) * pref_b (τ : ℂ)
    + 256 * ((∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ 16 * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ 4) ^ (n + 1))) ^ 32)
        * pref_c (τ : ℂ)

theorem F2p_complex :
    HahnSeries.ofPowerSeries ℤ ℂ (eisenstein4.map (Int.castRingHom ℂ)) *
          HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16 *
          qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 8) *
          qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16) =
      qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 48) +
        224 * HahnSeries.single (1 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 8 *
          qExpand ℂ 2 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 24) *
          qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16) +
        256 * HahnSeries.single (2 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 16 *
          qExpand ℂ 4 (HahnSeries.ofPowerSeries ℤ ℂ (etaProd.map (Int.castRingHom ℂ)) ^ 32) := by
  have hA := ((QS_eisenstein4.mul (QS_etaProd_pow 16)).mul (QS_qExpand_etaProd_pow 2 8)).mul
    (QS_qExpand_etaProd_pow 4 16)
  have hB := ((QS_qExpand_etaProd_pow 2 48).add
    (((((QS_ofNat 224).mul QS_single_one).mul (QS_etaProd_pow 8)).mul (QS_qExpand_etaProd_pow 2 24)).mul
      (QS_qExpand_etaProd_pow 4 16))).add
    ((((QS_ofNat 256).mul QS_single_two).mul (QS_etaProd_pow 16)).mul (QS_qExpand_etaProd_pow 4 32))
  refine hA.unique (fun τ => ?_)
  have h := hB τ
  beta_reduce
  rw [euler_F2p τ]
  exact h

end JMTransfer
end ModularCurve

end

set_option maxHeartbeats 1600000 in

theorem solution :
    HahnSeries.ofPowerSeries ℤ ℤ eisenstein4 * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 *
        qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8) * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) =
      qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 48) +
        224 * HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
          qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) +
        256 * HahnSeries.single (2 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 *
          qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 32) := by
  apply ModularCurve.laurentMap_injective (f := Int.castRingHom ℂ) Int.cast_injective
  have h := ModularCurve.JMTransfer.F2p_complex
  simp only [map_add, map_mul, map_pow, map_ofNat, ModularCurve.laurentMap_qExpand, ModularCurve.laurentMap_ofPowerSeries,
    ModularCurve.laurentMap_single, map_one] at h ⊢
  linear_combination h

end S_ModularCurve_eisenstein4_mul_etaProd_identity
end P2MW
export P2MW.S_ModularCurve_eisenstein4_mul_etaProd_identity (solution)
