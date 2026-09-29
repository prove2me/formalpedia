-- Prove2me | solution 1 for ModularForm.exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/93f47bff-f255-5fc7-a911-2d01d2f8749e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace WCuspOrdAux

theorem exists_tendsto_div_qParam_pow {Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ'.strictPeriods) (F : ModularForm Γ' k) (hF : F ≠ 0) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => F τ / Function.Periodic.qParam h τ ^ n) atImInfty (𝓝 a) := by
  have hper : Function.Periodic ((F : ℍ → ℂ) ∘ ofComplex) h := SlashInvariantFormClass.periodic_comp_ofComplex F hΓ
  have hG : AnalyticAt ℂ (cuspFunction h F) 0 := ModularFormClass.analyticAt_cuspFunction_zero F hh hΓ
  haveI : Fact (IsCusp OnePoint.infty Γ') := ⟨Γ'.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction h F z = 0 := by
    intro h0
    apply hF
    have hsum := fun τ : ℍ =>
      hasSum_qExpansion hh hper (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
    have hps := hasFPowerSeriesOnBall_cuspFunction hh hG hsum
    have hp0 := hps.hasFPowerSeriesAt.locally_zero_iff.mp h0
    rw [← ModularForm.qExpansion_eq_zero_iff hh hΓ F]
    ext m
    have e := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff m) hp0
    simp [FormalMultilinearSeries.coeff_ofScalars] at e
    exact e
  obtain ⟨n, g, hg, hg0, hfg⟩ := hG.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨n, g 0, hg0, ?_⟩
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam h τ) atImInfty (𝓝[≠] 0) :=
    (Function.Periodic.qParam_tendsto hh).comp UpperHalfPlane.tendsto_coe_atImInfty
  have hlim : Tendsto (fun z : ℂ => cuspFunction h F z / z ^ n) (𝓝[≠] 0) (𝓝 (g 0)) := by
    have hgc : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hgc.congr' ?_
    have hfg' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), cuspFunction h F z = (z - 0) ^ n • g z := hfg.filter_mono nhdsWithin_le_nhds
    filter_upwards [hfg', self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, mul_div_cancel_left₀ _ (pow_ne_zero n hz0')]
  refine (hlim.comp hq).congr (fun τ => ?_)
  simp only [Function.comp_apply]
  rw [UpperHalfPlane.eq_cuspFunction τ hh.ne' hper]

theorem mapGL_T_zpow (n : ℤ) :
    Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n) = Matrix.GeneralLinearGroup.upperRightHom (n : ℝ) := by
  simp only [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]

end WCuspOrdAux

open WCuspOrdAux in

theorem WCuspOrdAux.slash_main
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) := by
  let F := ModularForm.translate f (σ : GL (Fin 2) ℝ)
  have hΓ' : ((h : ℝ)) ∈ (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
      (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
      ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    refine Subgroup.mem_map.mpr ⟨σ * ModularGroup.T ^ h * σ⁻¹, hper, ?_⟩
    rw [map_mul, map_mul, map_inv, ← zpow_natCast, mapGL_T_zpow, Int.cast_natCast]
    rfl
  have hF : F ≠ 0 := by
    intro h0
    apply hf
    have hc : ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) = 0 := by
      have e1 : ((F : ℍ → ℂ)) = ((0 : ModularForm _ k) : ℍ → ℂ) := congrArg DFunLike.coe h0
      rw [ModularForm.coe_zero] at e1
      exact e1
    rw [← ModularForm.coe_eq_zero_iff]
    have e : (f : ℍ → ℂ) = ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) ∣[k] ((σ : GL (Fin 2) ℝ))⁻¹ := by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [e, hc, SlashAction.zero_slash]
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  obtain ⟨n, a, ha, hlim⟩ := exists_tendsto_div_qParam_pow hhR hΓ' F hF
  exact ⟨n, a, ha, hlim⟩

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) :=
  WCuspOrdAux.slash_main Γ k f hf σ h hh hper

#print axioms solution

end
end S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem
end P2MW
export P2MW.S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem (solution)
