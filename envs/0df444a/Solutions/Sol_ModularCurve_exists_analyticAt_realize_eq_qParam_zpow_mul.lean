-- Prove2me | solution 1 for ModularCurve.exists_analyticAt_realize_eq_qParam_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/777e9341-c869-541e-8b69-9aa262c2a442

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul
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

theorem C2Aux.cuspFunction_factor (N : ℕ) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ)
    (hn : ∀ j < n, PowerSeries.coeff j (qExpansion 1 (f : ℍ → ℂ)) = 0) :
    HasFPowerSeriesAt ((Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (f : ℍ → ℂ)))
        (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries 1 f)) 0 ∧
      (Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (f : ℍ → ℂ)) 0 =
        PowerSeries.coeff n (qExpansion 1 (f : ℍ → ℂ)) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction 1 (f : ℍ → ℂ) z =
        (z - 0) ^ n • (Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (f : ℍ → ℂ)) z := by
  have hP := C2Aux.hasFPowerSeriesAt_cuspFunction N f
  have hD := hP.has_fpower_series_iterate_dslope_fslope n
  refine ⟨hD, ?_, C2Aux.eq_pow_smul_iterate_dslope hP fun j hj => by
    rw [UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]; exact hn j hj⟩
  rw [← hD.coeff_zero 1]
  change (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries 1 f)).coeff 0 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]

theorem C2Aux.order_coe_eq {φ : PowerSeries ℂ} {n : ℕ} (hn : PowerSeries.coeff n φ ≠ 0)
    (hlt : ∀ i < n, PowerSeries.coeff i φ = 0) :
    (φ : LaurentSeries ℂ).order = n := by
  have key : ∀ j : ℤ, j < 0 → (φ : LaurentSeries ℂ).coeff j = 0 := fun j hj => by
    rw [HahnSeries.ofPowerSeries_apply]
    first
      | exact HahnSeries.embDomain_notin_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
      | exact HahnSeries.embDomain_notMem_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rwa [HahnSeries.ofPowerSeries_apply_coeff])
  · have hφ : (φ : LaurentSeries ℂ) ≠ 0 := fun h0 => hn (by
      have := congrArg (fun y : LaurentSeries ℂ => y.coeff (n : ℤ)) h0
      simpa [HahnSeries.ofPowerSeries_apply_coeff] using this)
    have hc : (φ : LaurentSeries ℂ).coeff (φ : LaurentSeries ℂ).order ≠ 0 := by
      rw [← HahnSeries.leadingCoeff_eq]; exact HahnSeries.leadingCoeff_ne_zero.mpr hφ
    by_contra hle
    have hlt' : (φ : LaurentSeries ℂ).order < n := not_le.mp hle
    rcases le_or_gt 0 (φ : LaurentSeries ℂ).order with h0 | h0
    · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le h0
      rw [hi, HahnSeries.ofPowerSeries_apply_coeff] at hc
      exact hc (hlt i (by omega))
    · exact hc (key _ h0)

theorem solution (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (hx : x ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      G 0 = (x : LaurentSeries ℂ).coeff (x : LaurentSeries ℂ).order ∧
      ∀ᶠ τ in atImInfty, ModularCurve.realize N (x : LaurentSeries ℂ) τ =
        Function.Periodic.qParam 1 (τ : ℂ) ^ (x : LaurentSeries ℂ).order *
          G (Function.Periodic.qParam 1 (τ : ℂ)) := by
  obtain ⟨k, g, h, hh0, hxhg⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N
      (x : LaurentSeries ℂ) x.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  have hx' : (x : LaurentSeries ℂ) ≠ 0 := by
    first
      | rwa [Ne, ZeroMemClass.coe_eq_zero]
      | exact fun h0 => hx (Subtype.ext h0)

  have hH0 : ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := fun h0 =>
    hh0 ((ModularForm.qExpansion_eq_zero_iff one_pos hΓ h).mp
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (by rwa [map_zero])))
  have hg0 : g ≠ 0 := by
    intro hg
    apply hx'
    have hG0 : ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [(ModularForm.qExpansion_eq_zero_iff one_pos hΓ g).mpr hg, map_zero]
    rw [hG0] at hxhg
    exact (mul_eq_zero.mp hxhg).resolve_right hH0

  set n : ℕ := (qExpansionFormalMultilinearSeries 1 h).order with hn_def
  set m : ℕ := (qExpansionFormalMultilinearSeries 1 g).order with hm_def
  have hHlt : ∀ j < n, PowerSeries.coeff j (qExpansion 1 (h : ℍ → ℂ)) = 0 := fun j hj => by
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, FormalMultilinearSeries.coeff_eq_zero]
    exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj
  have hGlt : ∀ j < m, PowerSeries.coeff j (qExpansion 1 (g : ℍ → ℂ)) = 0 := fun j hj => by
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, FormalMultilinearSeries.coeff_eq_zero]
    exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj

  obtain ⟨hDh, hDh_val, hFh⟩ := C2Aux.cuspFunction_factor N h n hHlt
  obtain ⟨hDg, hDg_val, hFg⟩ := C2Aux.cuspFunction_factor N g m hGlt
  set Dh : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[n] (cuspFunction 1 (h : ℍ → ℂ)) with hDh_def
  set Dg : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[m] (cuspFunction 1 (g : ℍ → ℂ)) with hDg_def
  have hph : qExpansionFormalMultilinearSeries 1 h ≠ 0 := by
    intro h0
    apply hh0
    rw [← ModularForm.qExpansion_eq_zero_iff one_pos hΓ]
    ext j
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, h0]
    simp [FormalMultilinearSeries.coeff]
  have hpg : qExpansionFormalMultilinearSeries 1 g ≠ 0 := by
    intro h0
    apply hg0
    rw [← ModularForm.qExpansion_eq_zero_iff one_pos hΓ]
    ext j
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, h0]
    simp [FormalMultilinearSeries.coeff]
  have hDh0 : Dh 0 ≠ 0 := (C2Aux.hasFPowerSeriesAt_cuspFunction N h).iterate_dslope_fslope_ne_zero hph
  have hDg0 : Dg 0 ≠ 0 := (C2Aux.hasFPowerSeriesAt_cuspFunction N g).iterate_dslope_fslope_ne_zero hpg

  have hordH : ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).order = n :=
    C2Aux.order_coe_eq (by rw [← hDh_val]; exact hDh0) hHlt
  have hordG : ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).order = m :=
    C2Aux.order_coe_eq (by rw [← hDg_val]; exact hDg0) hGlt
  have hord : (x : LaurentSeries ℂ).order = (m : ℤ) - n := by
    have := HahnSeries.order_mul hx' hH0
    rw [hxhg, hordG, hordH] at this
    omega
  have hlead : PowerSeries.coeff m (qExpansion 1 (g : ℍ → ℂ)) =
      (x : LaurentSeries ℂ).coeff (x : LaurentSeries ℂ).order *
        PowerSeries.coeff n (qExpansion 1 (h : ℍ → ℂ)) := by
    have := HahnSeries.leadingCoeff_mul (x : LaurentSeries ℂ)
      ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    rw [hxhg] at this
    simp only [HahnSeries.leadingCoeff_eq] at this
    rw [hordG, hordH, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff] at this
    exact this

  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  refine ⟨fun z => Dg z / Dh z, ?_, ?_, ?_⟩
  · exact hDg.analyticAt.div hDh.analyticAt hDh0
  · show Dg 0 / Dh 0 = _
    rw [hDg_val, hlead, ← hDh_val, mul_div_cancel_right₀ _ hDh0]
  · have h3 : ∀ᶠ z in 𝓝 (0 : ℂ), Dh z ≠ 0 := hDh.continuousAt.eventually_ne hDh0
    filter_upwards [hq.eventually hFh, hq.eventually hFg, hq.eventually h3] with τ h1 h2 h3
    have hqne : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    have hhτ : (h : ℍ → ℂ) τ =
        Function.Periodic.qParam 1 (τ : ℂ) ^ n * Dh (Function.Periodic.qParam 1 (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction h τ hΓ one_ne_zero, h1, sub_zero, smul_eq_mul]
    have hgτ : (g : ℍ → ℂ) τ =
        Function.Periodic.qParam 1 (τ : ℂ) ^ m * Dg (Function.Periodic.qParam 1 (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction g τ hΓ one_ne_zero, h2, sub_zero, smul_eq_mul]
    have hhne : (h : ℍ → ℂ) τ ≠ 0 := by
      rw [hhτ]; exact mul_ne_zero (pow_ne_zero _ hqne) h3
    rw [ModularCurve.realize_eq_div N g h (x : LaurentSeries ℂ) hxhg τ hhne, hgτ, hhτ, hord,
      zpow_natCast_sub_natCast₀ hqne, mul_div_mul_comm]

end S_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul
end P2MW
export P2MW.S_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul (solution)
