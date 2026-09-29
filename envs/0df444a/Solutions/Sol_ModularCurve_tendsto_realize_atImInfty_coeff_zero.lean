-- Prove2me | solution 1 for ModularCurve.tendsto_realize_atImInfty_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3f419b06-de53-5b2c-bf17-f9dcdceb20cb

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_tendsto_realize_atImInfty_coeff_zero
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

open UpperHalfPlane Filter
open scoped Topology

theorem C2Aux.eq_pow_smul_iterate_dslope {p : FormalMultilinearSeries ℂ ℂ ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    {n : ℕ} (hp : HasFPowerSeriesAt f p z₀) (hn : ∀ k < n, p.coeff k = 0) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (hp.has_fpower_series_iterate_dslope_fslope n)
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 hn
  convert hs1.symm
  simp only [FormalMultilinearSeries.coeff_iterate_fslope] at hx1
  exact hx1.unique hs2

theorem C2Aux.hasFPowerSeriesAt_cuspFunction (N : ℕ) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    HasFPowerSeriesAt (cuspFunction 1 (f : ℍ → ℂ)) (qExpansionFormalMultilinearSeries 1 f) 0 := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact (UpperHalfPlane.hasFPowerSeries_cuspFunction f
    (c := fun m => PowerSeries.coeff m (qExpansion 1 (f : ℍ → ℂ))) one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ) fun τ =>
      UpperHalfPlane.hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ).hasFPowerSeriesAt

theorem solution (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hx : 0 ≤ (x : LaurentSeries ℂ).order) :
    Filter.Tendsto (fun τ : ℍ => ModularCurve.realize N (x : LaurentSeries ℂ) τ) atImInfty
      (𝓝 ((x : LaurentSeries ℂ).coeff 0)) := by
  obtain ⟨k, g, h, hh0, hxhg⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N
      (x : LaurentSeries ℂ) x.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _

  have hPh := C2Aux.hasFPowerSeriesAt_cuspFunction N h
  have hPg := C2Aux.hasFPowerSeriesAt_cuspFunction N g
  set n : ℕ := (qExpansionFormalMultilinearSeries 1 h).order with hn_def
  have hph : qExpansionFormalMultilinearSeries 1 h ≠ 0 := by
    intro h0
    apply hh0
    rw [← ModularForm.qExpansion_eq_zero_iff one_pos hΓ]
    ext m
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, h0]
    simp [FormalMultilinearSeries.coeff]
  set Dh : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (h : ℍ → ℂ)) with hDh_def
  set Dg : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (g : ℍ → ℂ)) with hDg_def
  have hDh : HasFPowerSeriesAt Dh _ 0 := hPh.has_fpower_series_iterate_dslope_fslope n
  have hDg : HasFPowerSeriesAt Dg _ 0 := hPg.has_fpower_series_iterate_dslope_fslope n
  have hDh0 : Dh 0 ≠ 0 := hPh.iterate_dslope_fslope_ne_zero hph
  have hFh : ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction 1 (h : ℍ → ℂ) z = (z - 0) ^ n • Dh z :=
    C2Aux.eq_pow_smul_iterate_dslope hPh fun j hj => by
      rw [FormalMultilinearSeries.coeff_eq_zero]
      exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj

  have hDh_val : Dh 0 = PowerSeries.coeff n (qExpansion 1 (h : ℍ → ℂ)) := by
    rw [← hDh.coeff_zero 1]
    change (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries 1 h)).coeff 0 = _
    rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
      UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]
  have hDg_val : Dg 0 = PowerSeries.coeff n (qExpansion 1 (g : ℍ → ℂ)) := by
    rw [← hDg.coeff_zero 1]
    change (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries 1 g)).coeff 0 = _
    rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
      UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]

  have hHlt : ∀ j < n, PowerSeries.coeff j (qExpansion 1 (h : ℍ → ℂ)) = 0 := fun j hj => by
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, FormalMultilinearSeries.coeff_eq_zero]
    exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj

  set X : PowerSeries ℂ := PowerSeries.mk fun m : ℕ => (x : LaurentSeries ℂ).coeff (m : ℤ) with hX_def
  have hX : HahnSeries.ofPowerSeries ℤ ℂ X = (x : LaurentSeries ℂ) := by
    ext m
    rcases le_or_gt 0 m with hm | hm
    · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      simp [X]
    · rw [HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hm hx),
        HahnSeries.ofPowerSeries_apply]
      first
        | exact HahnSeries.embDomain_notin_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
        | exact HahnSeries.embDomain_notMem_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
  have hXH : X * qExpansion 1 (h : ℍ → ℂ) = qExpansion 1 (g : ℍ → ℂ) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_mul, hX]
    exact hxhg
  have hGcoeff : ∀ m ≤ n, PowerSeries.coeff m (qExpansion 1 (g : ℍ → ℂ)) =
      PowerSeries.coeff 0 X * PowerSeries.coeff m (qExpansion 1 (h : ℍ → ℂ)) := by
    intro m hm
    rw [← hXH, PowerSeries.coeff_mul, Finset.sum_eq_single (0, m)]
    · intro p hp hne
      have hp2 : p.2 < n := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rcases p with ⟨i, j⟩
        simp only [ne_eq, Prod.mk.injEq, not_and] at hne hp ⊢
        omega
      rw [hHlt _ hp2, mul_zero]
    · intro habs
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) habs
  have hGlt : ∀ j < n, (qExpansionFormalMultilinearSeries 1 g).coeff j = 0 := fun j hj => by
    rw [UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, hGcoeff j hj.le, hHlt j hj, mul_zero]
  have hFg : ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction 1 (g : ℍ → ℂ) z = (z - 0) ^ n • Dg z :=
    C2Aux.eq_pow_smul_iterate_dslope hPg hGlt
  have hx0 : (x : LaurentSeries ℂ).coeff 0 = PowerSeries.coeff 0 X := by
    simp [X]
  have hval : Dg 0 / Dh 0 = (x : LaurentSeries ℂ).coeff 0 := by
    rw [hDg_val, hGcoeff n le_rfl, ← hDh_val, mul_div_cancel_right₀ _ hDh0, hx0]

  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hlim : Tendsto (fun τ : ℍ => Dg (Function.Periodic.qParam 1 (τ : ℂ)) /
      Dh (Function.Periodic.qParam 1 (τ : ℂ))) atImInfty (𝓝 (Dg 0 / Dh 0)) :=
    (hDg.continuousAt.tendsto.comp hq).div (hDh.continuousAt.tendsto.comp hq) hDh0
  have hev : (fun τ : ℍ => Dg (Function.Periodic.qParam 1 (τ : ℂ)) /
      Dh (Function.Periodic.qParam 1 (τ : ℂ))) =ᶠ[atImInfty]
      fun τ : ℍ => ModularCurve.realize N (x : LaurentSeries ℂ) τ := by
    have h3 : ∀ᶠ z in 𝓝 (0 : ℂ), Dh z ≠ 0 := hDh.continuousAt.eventually_ne hDh0
    filter_upwards [hq.eventually hFh, hq.eventually hFg, hq.eventually h3] with τ h1 h2 h3
    have hqne : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    have hhτ : (h : ℍ → ℂ) τ = Function.Periodic.qParam 1 (τ : ℂ) ^ n * Dh (Function.Periodic.qParam 1 (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction h τ hΓ one_ne_zero, h1, sub_zero, smul_eq_mul]
    have hgτ : (g : ℍ → ℂ) τ = Function.Periodic.qParam 1 (τ : ℂ) ^ n * Dg (Function.Periodic.qParam 1 (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction g τ hΓ one_ne_zero, h2, sub_zero, smul_eq_mul]
    have hhne : (h : ℍ → ℂ) τ ≠ 0 := by
      rw [hhτ]; exact mul_ne_zero (pow_ne_zero _ hqne) h3
    rw [ModularCurve.realize_eq_div N g h (x : LaurentSeries ℂ) hxhg τ hhne, hgτ, hhτ,
      mul_div_mul_left _ _ (pow_ne_zero _ hqne)]
  rw [← hval]
  exact hlim.congr' hev

end S_ModularCurve_tendsto_realize_atImInfty_coeff_zero
end P2MW
export P2MW.S_ModularCurve_tendsto_realize_atImInfty_coeff_zero (solution)
