-- Prove2me | solution 1 for ModularCurve.hasSum_modularUnitSeries_inv_qParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f9629ac6-6abf-5917-9fe2-360cbd0c5e44

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function HahnSeries
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "dedekindEtaUnitQ deltaSeries isMonicOfOrder_deltaSeries deltaSeries_ne_zero deltaSeriesN isMonicOfOrder_deltaSeriesN modularUnitSeries qExpand_coeff_mul qExpand_coeff_of_not_dvd dedekindEtaUnit ofPowerSeries_coeff_of_neg qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit hasSum_qParam_mul_laurent laurent_qParam_coeff_unique"
p2m_open "ModularCurve"

namespace QexpN

private def ratNRH : ℚ →ₙ+* ℂ := (Rat.castHom ℂ).toNonUnitalRingHom

private def theta (x : LaurentSeries ℚ) : LaurentSeries ℂ := x.map ratNRH

private theorem theta_coeff (x : LaurentSeries ℚ) (m : ℤ) :
    (theta x).coeff m = ((x.coeff m : ℚ) : ℂ) := rfl

private theorem theta_mul (x y : LaurentSeries ℚ) : theta (x * y) = theta x * theta y :=
  HahnSeries.map_mul ratNRH

private def gfun (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

private lemma differentiableOn_gfun : DifferentiableOn ℂ gfun (Metric.ball (0 : ℂ) 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

private lemma gfun_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : gfun q ≠ 0 := by
  rw [gfun, (ModularForm.multipliable_one_sub_pow hq).tprod_pow]
  refine pow_ne_zero _ (tprod_one_add_ne_zero_of_summable (f := fun n => -q ^ (n + 1)) ?_ ?_)
  · intro i
    have h1 : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero i)
    intro h
    rw [add_neg_eq_zero] at h
    rw [← h, norm_one] at h1
    exact lt_irrefl _ h1
  · simpa [summable_nat_add_iff 1] using summable_geometric_of_lt_one (norm_nonneg _) hq

private lemma discriminant_eq_qParam_mul_gfun (τ : ℍ) :
    ModularForm.discriminant τ = 𝕢 1 (τ : ℂ) * gfun (𝕢 1 (τ : ℂ)) := by
  rw [ModularForm.discriminant_eq_q_prod, gfun]

private theorem hasSum_single_mul_coe_iff (k : ℤ) (P : PowerSeries ℂ) {q : ℂ} (hq : q ≠ 0) (t : ℂ) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) (t * q ^ k) ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) t := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) ∘
        (fun n : ℕ => (n : ℤ) + k) = fun n : ℕ => (PowerSeries.coeff n P * q ^ n) * q ^ k := by
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
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe, if_pos hmk,
      zero_mul]

private theorem hasSum_theta_deltaSeries (τ : ℍ) :
    HasSum (fun m : ℤ => (theta deltaSeries).coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant τ) := by
  have hper : Function.Periodic (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  have hmdiff := ModularFormClass.holo CuspForm.discriminant
  have hbdd : IsBoundedAtImInfty ModularForm.discriminant :=
    ModularForm.discriminant_isZeroAtImInfty.boundedAtFilter
  have h := hasSum_qExpansion one_pos hper hmdiff hbdd τ
  rw [ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at h
  have hinj : Function.Injective ((↑) : ℕ → ℤ) := fun a b hab => by exact_mod_cast hab
  rw [← hinj.hasSum_iff]
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, theta_coeff, smul_eq_mul]
    rcases n with - | k
    · rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) from rfl, deltaSeries, HahnSeries.coeff_single_mul, one_mul,
        ModularCurve.ofPowerSeries_coeff_of_neg _ (by norm_num), PowerSeries.coeff_map,
        PowerSeries.coeff_zero_X_mul]
      norm_num
    · rw [deltaSeries, HahnSeries.coeff_single_mul, one_mul,
        show ((k + 1 : ℕ) : ℤ) - 1 = ((k : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, dedekindEtaUnitQ, PowerSeries.coeff_map,
        PowerSeries.coeff_map, PowerSeries.coeff_succ_X_mul, zpow_natCast, eq_intCast,
        eq_intCast, Rat.cast_intCast]
  · intro m hm
    have hm' : m < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨m.toNat, by simp; omega⟩
    rw [theta_coeff, ModularCurve.isMonicOfOrder_deltaSeries.coeff_of_lt (by omega),
      Rat.cast_zero, zero_mul]

private theorem qParam_heckeDiagMatrix_smul {N : ℕ} (hN : N ≠ 0) (τ : ℍ) :
    𝕢 1 ((ModularForm.heckeDiagMatrix N • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ N := by
  rw [ModularForm.coe_heckeDiagMatrix_smul hN, Periodic.qParam, Periodic.qParam,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem hasSum_theta_deltaSeriesN (N : ℕ) [NeZero N] (τ : ℍ) :
    HasSum (fun m : ℤ => (theta (deltaSeriesN N)).coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hNZ : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN
  have h := hasSum_theta_deltaSeries (ModularForm.heckeDiagMatrix N • τ)
  have e : 𝕢 1 ((ModularForm.heckeDiagMatrix N • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ ((N : ℕ) : ℤ) := by
    rw [qParam_heckeDiagMatrix_smul hN, zpow_natCast]
  have hinj : Function.Injective (fun m : ℤ => ((N : ℕ) : ℤ) * m) := mul_right_injective₀ hNZ
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (theta (deltaSeriesN N)).coeff m * 𝕢 1 (τ : ℂ) ^ m) ∘
        (fun m : ℤ => ((N : ℕ) : ℤ) * m)
        = fun m : ℤ => (theta deltaSeries).coeff m * 𝕢 1 ((ModularForm.heckeDiagMatrix N • τ : ℍ) : ℂ) ^ m := by
      funext m
      simp only [Function.comp_apply, theta_coeff, deltaSeriesN]
      rw [ModularCurve.qExpand_coeff_mul, e, ← zpow_mul]
    rw [hfg]
    exact h
  · intro m hm
    rw [theta_coeff, deltaSeriesN,
      ModularCurve.qExpand_coeff_of_not_dvd N deltaSeries (fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩),
      Rat.cast_zero, zero_mul]

private theorem theta_deltaSeriesN_ne_zero (N : ℕ) [NeZero N] : theta (deltaSeriesN N) ≠ 0 := by
  have h1 : (theta (deltaSeriesN N)).coeff ((N : ℕ) : ℤ) = 1 := by
    rw [theta_coeff, (ModularCurve.isMonicOfOrder_deltaSeriesN N).coeff_self, Rat.cast_one]
  exact HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)

private theorem theta_deltaSeries_ne_zero : theta deltaSeries ≠ 0 := by
  have h1 : (theta deltaSeries).coeff (1 : ℤ) = 1 := by
    rw [theta_coeff, ModularCurve.isMonicOfOrder_deltaSeries.coeff_self, Rat.cast_one]
  exact HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)

private def phiFun (N : ℕ) : ℂ → ℂ := fun w => gfun w / gfun (w ^ N)

private def psiFun (N : ℕ) : ℂ → ℂ := fun w => gfun (w ^ N) / gfun w

private lemma pow_mem_ball {N : ℕ} [NeZero N] {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    w ^ N ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right] at hw ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw (NeZero.ne N)

private lemma differentiableOn_gfun_pow (N : ℕ) [NeZero N] :
    DifferentiableOn ℂ (fun w : ℂ => gfun (w ^ N)) (Metric.ball (0 : ℂ) 1) :=
  differentiableOn_gfun.comp ((differentiable_pow N).differentiableOn)
    fun _ hw => pow_mem_ball hw

private lemma differentiableOn_phiFun (N : ℕ) [NeZero N] :
    DifferentiableOn ℂ (phiFun N) (Metric.ball (0 : ℂ) 1) := by
  refine DifferentiableOn.div differentiableOn_gfun (differentiableOn_gfun_pow N)
    fun w hw => gfun_ne_zero ?_
  have := pow_mem_ball (N := N) hw
  rwa [Metric.mem_ball, dist_zero_right] at this

private lemma differentiableOn_psiFun (N : ℕ) [NeZero N] :
    DifferentiableOn ℂ (psiFun N) (Metric.ball (0 : ℂ) 1) := by
  refine DifferentiableOn.div (differentiableOn_gfun_pow N) differentiableOn_gfun
    fun w hw => gfun_ne_zero ?_
  rwa [Metric.mem_ball, dist_zero_right] at hw

private def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := ((n.factorial : ℂ))⁻¹ * iteratedDeriv n f 0

private lemma hasSum_taylorCoeff {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => taylorCoeff f n * q ^ n) (f q) := by
  have h := Complex.hasSum_taylorSeries_on_ball hf
    (show q ∈ Metric.ball (0 : ℂ) 1 by rwa [Metric.mem_ball, dist_zero_right])
  refine h.congr_fun fun n => ?_
  rw [taylorCoeff, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

private theorem modularUnitSeries_inv_mul (N : ℕ) [NeZero N] :
    (ModularCurve.modularUnitSeries N)⁻¹ * deltaSeries = deltaSeriesN N := by
  rw [ModularCurve.modularUnitSeries, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel₀ ModularCurve.deltaSeries_ne_zero, mul_one]

private theorem hasSum_modularUnitInv (N : ℕ) [NeZero N] (τ₀ : ℍ) :
    HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ)
        * 𝕢 1 (τ₀ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ₀)
        / ModularForm.discriminant τ₀) := by
  have hq0 : ∀ τ : ℍ, 𝕢 1 (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _
  have hqlt : ∀ τ : ℍ, ‖𝕢 1 (τ : ℂ)‖ < 1 := fun τ => by
    exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ
  set B : LaurentSeries ℂ := HahnSeries.single ((N : ℤ) - 1) 1
    * ((PowerSeries.mk (taylorCoeff (psiFun N)) : PowerSeries ℂ) : LaurentSeries ℂ) with hB
  have hval : ∀ τ : ℍ,
      ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ
      = psiFun N (𝕢 1 (τ : ℂ)) * 𝕢 1 (τ : ℂ) ^ ((N : ℤ) - 1) := by
    intro τ
    have hq := hq0 τ
    have hgq : gfun (𝕢 1 (τ : ℂ)) ≠ 0 := gfun_ne_zero (hqlt τ)
    have hgN : gfun (𝕢 1 (τ : ℂ) ^ N) ≠ 0 := gfun_ne_zero (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (hqlt τ) (NeZero.ne N))
    have hqN : 𝕢 1 (τ : ℂ) ^ N ≠ 0 := pow_ne_zero _ hq
    rw [discriminant_eq_qParam_mul_gfun τ,
      discriminant_eq_qParam_mul_gfun (ModularForm.heckeDiagMatrix N • τ),
      qParam_heckeDiagMatrix_smul (NeZero.ne N), psiFun, zpow_sub₀ hq, zpow_one, zpow_natCast]
    field_simp
  have hBsum : ∀ τ : ℍ, HasSum (fun m : ℤ => B.coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)
        / ModularForm.discriminant τ) := by
    intro τ
    rw [hval τ, hB]
    refine (hasSum_single_mul_coe_iff ((N : ℤ) - 1) _ (hq0 τ) _).mpr ?_
    refine (hasSum_taylorCoeff (differentiableOn_psiFun N) (hqlt τ)).congr_fun fun n => ?_
    rw [PowerSeries.coeff_mk]
  have hprod : ∀ τ : ℍ, HasSum
      (fun m : ℤ => (B * theta deltaSeries).coeff m * 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)) := by
    intro τ
    have h := ModularCurve.hasSum_qParam_mul_laurent 1 one_pos B (theta deltaSeries)
      (fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)
        / ModularForm.discriminant τ)
      (fun τ => ModularForm.discriminant τ)
      hBsum hasSum_theta_deltaSeries τ
    have h2 : HasSum (fun m : ℤ => (B * theta deltaSeries).coeff m * 𝕢 1 (τ : ℂ) ^ m)
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)
            / ModularForm.discriminant τ * ModularForm.discriminant τ) := h
    rwa [div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero _)] at h2
  have huniq : B * theta deltaSeries = theta (deltaSeriesN N) :=
    ModularCurve.laurent_qParam_coeff_unique 1 one_pos
      (fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)) _ _ hprod
      (hasSum_theta_deltaSeriesN N)
  have hTheta : theta ((ModularCurve.modularUnitSeries N)⁻¹) * theta deltaSeries
      = theta (deltaSeriesN N) := by
    rw [← theta_mul, modularUnitSeries_inv_mul]
  have hBu : B = theta ((ModularCurve.modularUnitSeries N)⁻¹) :=
    mul_right_cancel₀ theta_deltaSeries_ne_zero (huniq.trans hTheta.symm)
  have h := hBsum τ₀
  rw [hBu] at h
  refine h.congr_fun fun m => ?_
  rw [theta_coeff]

end QexpN

end ModularCurve

end

theorem solution (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ) :=
  ModularCurve.QexpN.hasSum_modularUnitInv N τ

end S_ModularCurve_hasSum_modularUnitSeries_inv_qParam
end P2MW
export P2MW.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam (solution)
