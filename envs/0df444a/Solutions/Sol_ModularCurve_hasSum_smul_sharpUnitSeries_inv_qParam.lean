-- Prove2me | solution 1 for ModularCurve.hasSum_smul_sharpUnitSeries_inv_qParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fc06e0bf-278e-5832-ab8e-04b136660270

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_sharpUnitSeries_pow_sharpIndex
import Theorems.Thm_ModularCurve_isMonicOfOrder_sharpUnitSeries
import Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function HahnSeries
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "sharpIndex sharpExp sharpIndex_pos sharpExp_mul_sharpIndex two_mul_sharpExp_div_two sharpExp_mul_sub_one sharpUnitFun sharpUnitFun_apply sharpUnitSeries modularUnitSeries eisensteinNumerator coeffMap coeffMap_coeff hasSum_modularUnitSeries_qParam hasSum_qParam_mul_laurent laurent_qParam_coeff_unique sharpUnitSeries_pow_sharpIndex isMonicOfOrder_sharpUnitSeries discriminant_div_discriminant_heckeDiagMatrix_smul"
p2m_open "ModularCurve"

namespace EIT

abbrev θ : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (Rat.castHom ℂ)

theorem θ_coeff (x : LaurentSeries ℚ) (m : ℤ) : (θ x).coeff m = ((x.coeff m : ℚ) : ℂ) := by
  rw [θ, coeffMap_coeff, eq_ratCast]

def P (w : ℂ) : ℂ := ∏' m : ℕ, (1 - w ^ (m + 1))

lemma differentiableOn_P : DifferentiableOn ℂ P (Metric.ball (0 : ℂ) 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow

lemma P_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : P w ≠ 0 := by
  rw [P]
  refine tprod_one_add_ne_zero_of_summable (f := fun m => -w ^ (m + 1)) ?_ ?_
  · intro i h
    have h1 : ‖w ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw (Nat.succ_ne_zero i)
    rw [add_neg_eq_zero] at h
    rw [← h, norm_one] at h1
    exact lt_irrefl _ h1
  · simpa [summable_nat_add_iff 1] using summable_geometric_of_lt_one (norm_nonneg _) hw

lemma P_zero : P 0 = 1 := by
  simp [P]

lemma eta_eq_qParam_mul_P (z : ℂ) : η z = 𝕢 24 z * P (𝕢 1 z) := rfl

variable (ℓ : ℕ)

def Φ (w : ℂ) : ℂ := (P w / P (w ^ ℓ)) ^ sharpExp ℓ

lemma pow_mem_ball {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) (hℓ : ℓ ≠ 0) :
    w ^ ℓ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right] at hw ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw hℓ

lemma differentiableOn_Φ [NeZero ℓ] : DifferentiableOn ℂ (Φ ℓ) (Metric.ball (0 : ℂ) 1) := by
  refine DifferentiableOn.pow (DifferentiableOn.div differentiableOn_P
    (differentiableOn_P.comp (differentiable_pow ℓ).differentiableOn
      fun _ hw => pow_mem_ball ℓ hw (NeZero.ne ℓ)) fun w hw => P_ne_zero ?_) _
  have := pow_mem_ball ℓ hw (NeZero.ne ℓ)
  rwa [Metric.mem_ball, dist_zero_right] at this

lemma Φ_ne_zero [NeZero ℓ] {w : ℂ} (hw : ‖w‖ < 1) : Φ ℓ w ≠ 0 := by
  refine pow_ne_zero _ (div_ne_zero (P_ne_zero hw) (P_ne_zero ?_))
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw (NeZero.ne ℓ)

lemma differentiableOn_Φ_inv [NeZero ℓ] :
    DifferentiableOn ℂ (fun w => (Φ ℓ w)⁻¹) (Metric.ball (0 : ℂ) 1) :=
  DifferentiableOn.inv (differentiableOn_Φ ℓ) fun _ hw =>
    Φ_ne_zero ℓ (by rwa [Metric.mem_ball, dist_zero_right] at hw)

lemma Φ_zero [NeZero ℓ] : Φ ℓ 0 = 1 := by
  simp [Φ, P_zero, zero_pow (NeZero.ne ℓ)]

variable [NeZero ℓ]

lemma qParam_heckeDiagMatrix_smul (τ : ℍ) :
    𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ ℓ := by
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), Periodic.qParam, Periodic.qParam,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma qParam24_div_pow (τ : ℍ) :
    (𝕢 24 (τ : ℂ) / 𝕢 24 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ)) ^ sharpExp ℓ =
      𝕢 1 (τ : ℂ) ^ (-(eisensteinNumerator ℓ : ℤ)) := by
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
  have key : ((sharpExp ℓ : ℕ) : ℤ) * ((ℓ : ℤ) - 1) = 24 * (eisensteinNumerator ℓ : ℤ) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) (sharpExp_mul_sub_one ℓ)
    push_cast [Nat.cast_sub hℓ1] at this
    exact this
  set E : ℂ := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ) / 24) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have h24 : 𝕢 24 (τ : ℂ) = E := by
    rw [hE, Periodic.qParam]; push_cast; ring_nf
  have hℓq : 𝕢 24 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = E ^ ℓ := by
    rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), Periodic.qParam, hE, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1 : 𝕢 1 (τ : ℂ) = E ^ 24 := by
    rw [Periodic.qParam, hE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h24, hℓq, h1, show E / E ^ ℓ = E ^ ((1 : ℤ) - ℓ) by rw [zpow_sub₀ hE0, zpow_one, zpow_natCast],
    ← zpow_natCast, ← zpow_mul, ← zpow_natCast E 24, ← zpow_mul]
  congr 1
  push_cast
  linear_combination -key

lemma sharpUnitFun_eq_qParam_zpow_mul_Φ (τ : ℍ) :
    sharpUnitFun ℓ τ = 𝕢 1 (τ : ℂ) ^ (-(eisensteinNumerator ℓ : ℤ)) * Φ ℓ (𝕢 1 (τ : ℂ)) := by
  rw [sharpUnitFun_apply, eta_eq_qParam_mul_P, eta_eq_qParam_mul_P, mul_div_mul_comm, mul_pow,
    qParam24_div_pow, Φ, qParam_heckeDiagMatrix_smul]

omit [NeZero ℓ] in
lemma sharpUnitFun_ne_zero (τ : ℍ) : sharpUnitFun ℓ τ ≠ 0 := by
  rw [sharpUnitFun_apply]
  exact pow_ne_zero _ (div_ne_zero (ModularForm.eta_ne_zero τ.2)
    (ModularForm.eta_ne_zero (ModularForm.heckeDiagMatrix ℓ • τ).2))

omit [NeZero ℓ] in

lemma sharpUnitFun_pow_sharpIndex (τ : ℍ) :
    sharpUnitFun ℓ τ ^ sharpIndex ℓ =
      ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) := by
  rw [sharpUnitFun_apply, ← pow_mul, sharpExp_mul_sharpIndex, div_pow]
  rfl

omit [NeZero ℓ] in
theorem hasSum_single_mul_coe_iff (k : ℤ) (Q : PowerSeries ℂ) {q : ℂ} (hq : q ≠ 0) (t : ℂ) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (Q : LaurentSeries ℂ)).coeff m * q ^ m)
      (t * q ^ k) ↔ HasSum (fun n : ℕ => PowerSeries.coeff n Q * q ^ n) t := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (Q : LaurentSeries ℂ)).coeff m * q ^ m) ∘
        (fun n : ℕ => (n : ℤ) + k) = fun n : ℕ => (PowerSeries.coeff n Q * q ^ n) * q ^ k := by
      funext n
      simp only [Function.comp_apply]
      rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.coeff_coe_powerSeries, zpow_add₀ hq,
        zpow_natCast]
      ring
    rw [hfg]
    exact hasSum_mul_right_iff (zpow_ne_zero k hq)
  · intro m hm
    have hmk : m - k < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m - k).toNat, by simp only; omega⟩
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe,
      if_pos hmk, zero_mul]

omit [NeZero ℓ] in
def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := ((n.factorial : ℂ))⁻¹ * iteratedDeriv n f 0

omit [NeZero ℓ] in
lemma hasSum_taylorCoeff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun n : ℕ => taylorCoeff f n * q ^ n) (f q) := by
  have h := Complex.hasSum_taylorSeries_on_ball hf
    (show q ∈ Metric.ball (0 : ℂ) 1 by rwa [Metric.mem_ball, dist_zero_right])
  refine h.congr_fun fun n => ?_
  rw [taylorCoeff, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

omit [NeZero ℓ] in
lemma taylorCoeff_zero (f : ℂ → ℂ) : taylorCoeff f 0 = f 0 := by
  simp [taylorCoeff]

def bPS : PowerSeries ℂ := PowerSeries.mk (taylorCoeff (Φ ℓ))

def B : LaurentSeries ℂ :=
  HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℂ) * (bPS ℓ : LaurentSeries ℂ)

lemma constantCoeff_bPS : PowerSeries.constantCoeff (bPS ℓ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, bPS, PowerSeries.coeff_mk, taylorCoeff_zero, Φ_zero]

lemma hq0 (τ : ℍ) : 𝕢 1 (τ : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
lemma hqlt (τ : ℍ) : ‖𝕢 1 (τ : ℂ)‖ < 1 := by exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ

theorem hasSum_B (τ : ℍ) :
    HasSum (fun m : ℤ => (B ℓ).coeff m * 𝕢 1 (τ : ℂ) ^ m) (sharpUnitFun ℓ τ) := by
  rw [sharpUnitFun_eq_qParam_zpow_mul_Φ, mul_comm, B]
  refine (hasSum_single_mul_coe_iff _ _ (hq0 τ) _).mpr ?_
  refine (hasSum_taylorCoeff (differentiableOn_Φ ℓ) (hqlt τ)).congr_fun fun n => ?_
  rw [bPS, PowerSeries.coeff_mk]

theorem hasSum_B_pow (j : ℕ) (τ : ℍ) :
    HasSum (fun m : ℤ => (B ℓ ^ j).coeff m * 𝕢 1 (τ : ℂ) ^ m) (sharpUnitFun ℓ τ ^ j) := by
  induction j generalizing τ with
  | zero =>
    simp only [pow_zero]
    have : (fun m : ℤ => (1 : LaurentSeries ℂ).coeff m * 𝕢 1 (τ : ℂ) ^ m) =
        fun m : ℤ => if m = 0 then 1 else 0 := by
      funext m
      rw [← HahnSeries.single_zero_one, HahnSeries.coeff_single]
      split_ifs with h
      · subst h; simp
      · simp
    rw [this]
    exact hasSum_ite_eq 0 1
  | succ j ih =>
    simp only [pow_succ]
    exact ModularCurve.hasSum_qParam_mul_laurent 1 one_pos (B ℓ ^ j) (B ℓ) (fun τ => sharpUnitFun ℓ τ ^ j)
      (sharpUnitFun ℓ) ih (hasSum_B ℓ) τ

private abbrev _root_.ModularCurve.EIT.S : LaurentSeries ℂ := θ (sharpUnitSeries ℓ)

p2m_export "ModularCurve.EIT" "S"
lemma S_coeff_neg : (S ℓ).coeff (-(eisensteinNumerator ℓ : ℤ)) = 1 := by
  have h := ModularCurve.isMonicOfOrder_sharpUnitSeries ℓ
  rw [θ_coeff, ← h.1, ← HahnSeries.leadingCoeff_eq, h.2, Rat.cast_one]

lemma S_coeff_of_lt {j : ℤ} (hj : j < -(eisensteinNumerator ℓ : ℤ)) : (S ℓ).coeff j = 0 := by
  have h := ModularCurve.isMonicOfOrder_sharpUnitSeries ℓ
  rw [θ_coeff, HahnSeries.coeff_eq_zero_of_lt_order (by rw [h.1]; exact hj), Rat.cast_zero]

lemma S_ne_zero : S ℓ ≠ 0 := fun h => by simpa [h] using S_coeff_neg ℓ

lemma S_order : (S ℓ).order = -(eisensteinNumerator ℓ : ℤ) := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [S_coeff_neg]; exact one_ne_zero)) ?_
  by_contra h
  push Not at h
  exact S_ne_zero ℓ (HahnSeries.coeff_order_eq_zero.mp (S_coeff_of_lt ℓ h))

def sPS : PowerSeries ℂ := (S ℓ).powerSeriesPart

lemma S_eq : S ℓ = HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℂ) * (sPS ℓ : LaurentSeries ℂ) := by
  rw [sPS, LaurentSeries.ofPowerSeries_powerSeriesPart, S_order, neg_neg, ← mul_assoc,
    HahnSeries.single_mul_single, neg_add_cancel, one_mul, ← HahnSeries.C_apply, HahnSeries.C_one, one_mul]

lemma constantCoeff_sPS : PowerSeries.constantCoeff (sPS ℓ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sPS, LaurentSeries.powerSeriesPart_coeff, S_order,
    Nat.cast_zero, add_zero, S_coeff_neg]

lemma eq_of_pow_eq_pow {b s : PowerSeries ℂ} {k : ℕ} (hk : 0 < k)
    (hb : PowerSeries.constantCoeff b = 1) (hs : PowerSeries.constantCoeff s = 1) (h : b ^ k = s ^ k) :
    b = s := by
  have hfac := geom_sum₂_mul b s k
  rw [h, sub_self] at hfac
  have hne : (∑ i ∈ Finset.range k, b ^ i * s ^ (k - 1 - i)) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [map_sum, map_zero] at this
    simp only [map_mul, map_pow, hb, hs, one_pow, mul_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at this
    exact (Nat.cast_ne_zero.mpr hk.ne') this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hne)

theorem B_eq_S : B ℓ = S ℓ := by

  have hk : 0 < sharpIndex ℓ := sharpIndex_pos ℓ
  have h1 : ∀ τ : ℍ, HasSum (fun m : ℤ => (B ℓ ^ sharpIndex ℓ).coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) :=
    fun τ => sharpUnitFun_pow_sharpIndex ℓ τ ▸ hasSum_B_pow ℓ (sharpIndex ℓ) τ
  have h2 : ∀ τ : ℍ, HasSum (fun m : ℤ => (S ℓ ^ sharpIndex ℓ).coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) := by
    intro τ
    have h := ModularCurve.hasSum_modularUnitSeries_qParam ℓ τ
    rw [← ModularCurve.sharpUnitSeries_pow_sharpIndex] at h
    refine h.congr_fun fun m => ?_
    rw [S, ← map_pow, θ_coeff]
  have hpow : B ℓ ^ sharpIndex ℓ = S ℓ ^ sharpIndex ℓ :=
    ModularCurve.laurent_qParam_coeff_unique 1 one_pos _ _ _ h1 h2

  rw [B, S_eq, mul_pow, mul_pow] at hpow
  have hunit : (HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℂ)) ^ sharpIndex ℓ ≠ 0 :=
    pow_ne_zero _ (by simp)
  have hps : ((bPS ℓ ^ sharpIndex ℓ : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((sPS ℓ ^ sharpIndex ℓ : PowerSeries ℂ) : LaurentSeries ℂ) := by
    simpa [map_pow] using mul_left_cancel₀ hunit hpow
  have hbs : bPS ℓ = sPS ℓ :=
    eq_of_pow_eq_pow hk (constantCoeff_bPS ℓ) (constantCoeff_sPS ℓ)
      (HahnSeries.ofPowerSeries_injective hps)
  rw [B, S_eq, hbs]

theorem hasSum_sharpUnitSeries (τ : ℍ) :
    HasSum (fun m : ℤ => (((sharpUnitSeries ℓ).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (sharpUnitFun ℓ τ) := by
  have h := hasSum_B ℓ τ
  rw [B_eq_S] at h
  refine h.congr_fun fun m => ?_
  rw [θ_coeff]

def B' : LaurentSeries ℂ :=
  HahnSeries.single ((eisensteinNumerator ℓ : ℤ)) (1 : ℂ) *
    ((PowerSeries.mk (taylorCoeff fun w => (Φ ℓ w)⁻¹) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem hasSum_B' (τ : ℍ) :
    HasSum (fun m : ℤ => (B' ℓ).coeff m * 𝕢 1 (τ : ℂ) ^ m) ((sharpUnitFun ℓ τ)⁻¹) := by
  have hval : (sharpUnitFun ℓ τ)⁻¹ = (Φ ℓ (𝕢 1 (τ : ℂ)))⁻¹ * 𝕢 1 (τ : ℂ) ^ ((eisensteinNumerator ℓ : ℤ)) := by
    rw [sharpUnitFun_eq_qParam_zpow_mul_Φ, mul_inv, zpow_neg, inv_inv, mul_comm]
  rw [hval, B']
  refine (hasSum_single_mul_coe_iff _ _ (hq0 τ) _).mpr ?_
  refine (hasSum_taylorCoeff (differentiableOn_Φ_inv ℓ) (hqlt τ)).congr_fun fun n => ?_
  rw [PowerSeries.coeff_mk]

theorem B'_eq : B' ℓ = (S ℓ)⁻¹ := by
  have h1 : ∀ τ : ℍ, HasSum (fun m : ℤ => (S ℓ * B' ℓ).coeff m * 𝕢 1 (τ : ℂ) ^ m) (1 : ℂ) := by
    intro τ
    have h := ModularCurve.hasSum_qParam_mul_laurent 1 one_pos (S ℓ) (B' ℓ) (sharpUnitFun ℓ)
      (fun τ => (sharpUnitFun ℓ τ)⁻¹) (fun τ => B_eq_S ℓ ▸ hasSum_B ℓ τ) (hasSum_B' ℓ) τ
    rwa [mul_inv_cancel₀ (sharpUnitFun_ne_zero ℓ τ)] at h
  have h2 : ∀ τ : ℍ, HasSum (fun m : ℤ => (1 : LaurentSeries ℂ).coeff m * 𝕢 1 (τ : ℂ) ^ m) (1 : ℂ) := by
    intro τ
    have : (fun m : ℤ => (1 : LaurentSeries ℂ).coeff m * 𝕢 1 (τ : ℂ) ^ m) =
        fun m : ℤ => if m = 0 then 1 else 0 := by
      funext m
      rw [← HahnSeries.single_zero_one, HahnSeries.coeff_single]
      split_ifs with h
      · subst h; simp
      · simp
    rw [this]; exact hasSum_ite_eq 0 1
  have h := ModularCurve.laurent_qParam_coeff_unique 1 one_pos (fun _ => (1 : ℂ)) _ _ h1 h2
  exact eq_inv_of_mul_eq_one_right h

theorem hasSum_sharpUnitSeries_inv (τ : ℍ) :
    HasSum (fun m : ℤ => ((((sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      ((sharpUnitFun ℓ τ)⁻¹) := by
  have h := hasSum_B' ℓ τ
  rw [B'_eq, S, ← map_inv₀] at h
  refine h.congr_fun fun m => ?_
  rw [θ_coeff]

theorem sharpUnitFun_eq_of_qParam_eq {τ τ' : ℍ} (h : 𝕢 1 (τ : ℂ) = 𝕢 1 (τ' : ℂ)) :
    sharpUnitFun ℓ τ = sharpUnitFun ℓ τ' := by
  have h1 := hasSum_sharpUnitSeries ℓ τ
  have h2 := hasSum_sharpUnitSeries ℓ τ'
  rw [h] at h1
  exact h1.unique h2

theorem sharpUnitFun_T_smul (τ : ℍ) : sharpUnitFun ℓ (ModularGroup.T • τ) = sharpUnitFun ℓ τ := by
  refine sharpUnitFun_eq_of_qParam_eq ℓ ?_
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, Periodic.qParam, Periodic.qParam]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 + (τ : ℂ)) / 1 =
      2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / 1 + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

omit [NeZero ℓ] in
lemma csqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

omit [NeZero ℓ] in

lemma eta_S_sq (z : ℍ) : η (-(z : ℂ)⁻¹) ^ 2 = -Complex.I * (z : ℂ) * η (z : ℂ) ^ 2 := by
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using ModularForm.eta_comp_eq_csqrt_I_inv z.2
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_sq, csqrt_sq, Complex.inv_I]
  ring

omit [NeZero ℓ] in
lemma eta_S_pow_sharpExp (z : ℍ) :
    η (-(z : ℂ)⁻¹) ^ sharpExp ℓ = (-Complex.I * (z : ℂ)) ^ (sharpExp ℓ / 2) * η (z : ℂ) ^ sharpExp ℓ := by
  conv_lhs => rw [← two_mul_sharpExp_div_two ℓ, pow_mul, eta_S_sq, mul_pow, ← pow_mul,
    two_mul_sharpExp_div_two]

def divNat (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) / ℓ, by
    rw [Complex.div_natCast_im]
    exact div_pos τ.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ℓ)))⟩

lemma coe_divNat (τ : ℍ) : ((divNat ℓ τ : ℍ) : ℂ) = (τ : ℂ) / ℓ := rfl

lemma heckeDiagMatrix_smul_divNat (τ : ℍ) : ModularForm.heckeDiagMatrix ℓ • divNat ℓ τ = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), coe_divNat,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))]

lemma qParam_divNat (τ : ℍ) : 𝕢 1 ((divNat ℓ τ : ℍ) : ℂ) = 𝕢 ℓ (τ : ℂ) := by
  rw [coe_divNat, Periodic.qParam, Periodic.qParam]
  congr 1
  push_cast
  ring

theorem sharpUnitFun_S_smul (τ : ℍ) :
    sharpUnitFun ℓ (ModularGroup.S • τ) = (ℓ : ℂ) ^ (sharpExp ℓ / 2) * (sharpUnitFun ℓ (divNat ℓ τ))⁻¹ := by
  have hτ : (τ : ℂ) ≠ 0 := ne_zero τ
  have hℓ : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hSD : ((ModularForm.heckeDiagMatrix ℓ • ModularGroup.S • τ : ℍ) : ℂ) = -(((divNat ℓ τ : ℍ) : ℂ))⁻¹ := by
    rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), hS, coe_divNat, inv_div]
    field_simp
  have hη1 : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hη2 : η ((divNat ℓ τ : ℍ) : ℂ) ≠ 0 := ModularForm.eta_ne_zero (divNat ℓ τ).2
  have hI : (-Complex.I * (τ : ℂ)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ
  rw [sharpUnitFun_apply, hS, hSD, div_pow, eta_S_pow_sharpExp ℓ τ, eta_S_pow_sharpExp ℓ (divNat ℓ τ),
    sharpUnitFun_apply, heckeDiagMatrix_smul_divNat]
  rw [coe_divNat] at hη2 ⊢
  rw [show -Complex.I * ((τ : ℂ) / ℓ) = (-Complex.I * τ) / ℓ by ring, div_pow (-Complex.I * (τ : ℂ)) (ℓ : ℂ)]
  field_simp
  rw [div_pow, mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hη1)]

theorem hasSum_smul_sharpUnitSeries_inv (τ : ℍ) :
    HasSum (fun m : ℤ => (((((ℓ : ℚ) ^ (sharpExp ℓ / 2)) • (sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m)
      (sharpUnitFun ℓ (ModularGroup.S • τ)) := by
  rw [sharpUnitFun_S_smul]
  have h := hasSum_sharpUnitSeries_inv ℓ (divNat ℓ τ)
  rw [qParam_divNat] at h
  refine (h.mul_left ((ℓ : ℂ) ^ (sharpExp ℓ / 2))).congr_fun fun m => ?_
  rw [HahnSeries.coeff_smul, smul_eq_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, mul_assoc]

theorem hasSum_smul_sharpUnitSeries (τ : ℍ) :
    HasSum (fun m : ℤ => (((((ℓ : ℚ) ^ (sharpExp ℓ / 2))⁻¹ • sharpUnitSeries ℓ).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m)
      ((sharpUnitFun ℓ (ModularGroup.S • τ))⁻¹) := by
  rw [sharpUnitFun_S_smul, mul_inv, inv_inv]
  have h := hasSum_sharpUnitSeries ℓ (divNat ℓ τ)
  rw [qParam_divNat] at h
  refine (h.mul_left (((ℓ : ℂ) ^ (sharpExp ℓ / 2))⁻¹)).congr_fun fun m => ?_
  rw [HahnSeries.coeff_smul, smul_eq_mul, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, mul_assoc]

theorem sharpUnitFun_U_smul (τ : ℍ) :
    sharpUnitFun ℓ ((ModularGroup.S * ModularGroup.T ^ (-(ℓ : ℤ)) * ModularGroup.S⁻¹) • τ) = sharpUnitFun ℓ τ := by
  set σ : ℍ := ModularGroup.S⁻¹ • τ with hσ
  have hτ : τ = ModularGroup.S • σ := by rw [hσ, smul_inv_smul]
  rw [mul_smul, mul_smul, ← hσ, sharpUnitFun_S_smul, hτ, sharpUnitFun_S_smul]
  congr 2
  refine sharpUnitFun_eq_of_qParam_eq ℓ ?_
  rw [qParam_divNat, qParam_divNat, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    Periodic.qParam, Periodic.qParam]
  have hℓ : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(ℓ : ℂ) + (σ : ℂ)) / ℓ =
      2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ) / ℓ + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        field_simp; push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [NeZero ℓ] in
lemma continuous_sharpUnitFun : Continuous (sharpUnitFun ℓ) := by
  have hη : ContinuousOn η {z : ℂ | 0 < z.im} := fun z hz =>
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).continuousAt.continuousWithinAt
  have h1 : Continuous fun τ : ℍ => η (τ : ℂ) :=
    hη.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.2
  have h2' : Continuous fun τ : ℍ => ModularForm.heckeDiagMatrix ℓ • τ := continuous_const_smul _
  have h2 : Continuous fun τ : ℍ => η ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) := h1.comp h2'
  have : sharpUnitFun ℓ = fun τ : ℍ => (η (τ : ℂ) / η ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ)) ^ sharpExp ℓ :=
    rfl
  rw [this]
  exact (h1.div h2 fun τ : ℍ => ModularForm.eta_ne_zero (ModularForm.heckeDiagMatrix ℓ • τ).2).pow _

omit [NeZero ℓ] in
lemma continuous_sl_smul (γ : SL(2, ℤ)) : Continuous fun τ : ℍ => γ • τ := by
  have : (fun τ : ℍ => γ • τ) = fun τ : ℍ => (γ : GL (Fin 2) ℝ) • τ := funext fun τ => ModularGroup.sl_moeb γ τ
  rw [this]
  exact continuous_const_smul _

theorem exists_character_sharpUnitFun :
    ∃ χ : CongruenceSubgroup.Gamma0 ℓ →* ℂˣ, (∀ γ : CongruenceSubgroup.Gamma0 ℓ, (χ γ : ℂ) ^ sharpIndex ℓ = 1) ∧
      ∀ (γ : CongruenceSubgroup.Gamma0 ℓ) (τ : ℍ),
        sharpUnitFun ℓ ((γ : SL(2, ℤ)) • τ) = χ γ * sharpUnitFun ℓ τ := by

  let c : CongruenceSubgroup.Gamma0 ℓ → ℍ → ℂ := fun γ τ => sharpUnitFun ℓ ((γ : SL(2, ℤ)) • τ) / sharpUnitFun ℓ τ
  have hc : ∀ γ τ, c γ τ = sharpUnitFun ℓ ((γ : SL(2, ℤ)) • τ) / sharpUnitFun ℓ τ := fun _ _ => rfl
  have hne : ∀ γ τ, c γ τ ≠ 0 := fun γ τ => div_ne_zero (sharpUnitFun_ne_zero ℓ _) (sharpUnitFun_ne_zero ℓ _)
  have hck : ∀ γ τ, c γ τ ^ sharpIndex ℓ = 1 := by
    intro γ τ
    rw [hc, div_pow, sharpUnitFun_pow_sharpIndex, sharpUnitFun_pow_sharpIndex,
      ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ (γ : SL(2, ℤ)) γ.2 τ, div_self]
    exact div_ne_zero (ModularForm.discriminant_ne_zero _) (ModularForm.discriminant_ne_zero _)

  have hcont : ∀ γ, Continuous (c γ) := fun γ =>
    ((continuous_sharpUnitFun ℓ).comp (continuous_sl_smul (γ : SL(2, ℤ)))).div (continuous_sharpUnitFun ℓ)
      (sharpUnitFun_ne_zero ℓ)
  have hfin : ({z : ℂ | z ^ sharpIndex ℓ = 1} : Set ℂ).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet ((Polynomial.nthRoots (sharpIndex ℓ) (1 : ℂ)).toFinset)) ?_
    intro z hz
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (sharpIndex_pos ℓ)).mpr hz
  have hconst : ∀ γ τ τ', c γ τ = c γ τ' := fun γ τ τ' =>
    isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete (hcont γ).continuousOn
      (fun τ _ => hck γ τ) (Set.mem_univ τ) (Set.mem_univ τ')

  let τ₀ : ℍ := UpperHalfPlane.I
  refine ⟨MonoidHom.mk' (fun γ => Units.mk0 (c γ τ₀) (hne γ τ₀)) ?_, ?_, ?_⟩
  · intro γ γ'
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [hconst γ τ₀ ((γ' : SL(2, ℤ)) • τ₀), hc, hc, hc, Subgroup.coe_mul, mul_smul,
      div_mul_div_cancel₀ (sharpUnitFun_ne_zero ℓ _)]
  · intro γ
    simp only [MonoidHom.mk'_apply, Units.val_mk0]
    exact hck γ τ₀
  · intro γ τ
    simp only [MonoidHom.mk'_apply, Units.val_mk0]
    rw [hconst γ τ₀ τ, hc, div_mul_cancel₀ _ (sharpUnitFun_ne_zero ℓ τ)]

end EIT

end ModularCurve

end

theorem solution (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ℓ : ℚ) ^ (ModularCurve.sharpExp ℓ / 2) • (ModularCurve.sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (ModularCurve.sharpUnitFun ℓ (ModularGroup.S • τ)) :=
  ModularCurve.EIT.hasSum_smul_sharpUnitSeries_inv ℓ τ

end S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam
end P2MW
export P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam (solution)
