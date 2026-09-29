-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f7fa573a-1836-5bb1-8dce-bd8efa8ef20f

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane Filter ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve"
open scoped MatrixGroups Topology Manifold

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf laurentBaseChange realize translation_mem_GammaH xHFunctionField realizeOf_eq_div qExpansion_div_mem_laurentBaseChange_xHFunctionField"
namespace ComplexPlaceDictionaryOfOrbitH
p2m_open "ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL {k : ℤ} (f : ModularForm Γ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have h : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map h

theorem continuous_coe {k : ℤ} (f : ModularForm Γ k) : Continuous (f : ℍ → ℂ) :=
  (ModularFormClass.holo f).continuous

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm Γ k) : (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem ne_zero_of_apply_ne_zero {k : ℤ} (f : ModularForm Γ k) {τ : ℍ} (h : (f : ℍ → ℂ) τ ≠ 0) :
    f ≠ 0 := by
  rintro rfl
  exact h rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) (τ : ℍ) :
    ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem exists_normalised_pair {k : ℤ} (g h : ModularForm Γ k) {τ τ' : ℍ}
    (hdet : (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ) :
    ∃ g₁ h₁ : ModularForm Γ k,
      (h₁ : ℍ → ℂ) τ ≠ 0 ∧ (h₁ : ℍ → ℂ) τ' = 0 ∧ (g₁ : ℍ → ℂ) τ' ≠ 0 := by
  set h₁ : ModularForm Γ k := ((h : ℍ → ℂ) τ') • g - ((g : ℍ → ℂ) τ') • h with hh₁
  have hval : ∀ z : ℍ, (h₁ : ℍ → ℂ) z =
      (h : ℍ → ℂ) τ' * (g : ℍ → ℂ) z - (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) z := by
    intro z
    simp [hh₁, smul_eq_mul]
  have h₁τ : (h₁ : ℍ → ℂ) τ ≠ 0 := by
    rw [hval]
    intro h0
    apply hdet
    have := sub_eq_zero.mp h0
    calc (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' = (h : ℍ → ℂ) τ' * (g : ℍ → ℂ) τ := by ring
      _ = (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := this
  have h₁τ' : (h₁ : ℍ → ℂ) τ' = 0 := by
    rw [hval]; ring
  by_cases hg : (g : ℍ → ℂ) τ' = 0
  · refine ⟨h, h₁, h₁τ, h₁τ', ?_⟩
    intro hh0
    apply hdet
    rw [hg, hh0, mul_zero, zero_mul]
  · exact ⟨g, h₁, h₁τ, h₁τ', hg⟩

section Local

variable (hT : ModularGroup.T ∈ Γ) {k : ℤ} (g₁ h₁ : ModularForm Γ k)

def quot : LaurentSeries ℂ := qL g₁ / qL h₁

include hT in
theorem quot_mul_eq (hh₁ : h₁ ≠ 0) : quot g₁ h₁ * qL h₁ = qL g₁ :=
  div_mul_cancel₀ _ (qL_ne_zero hT h₁ hh₁)

include hT in
theorem realizeOf_quot_eq (hh₁ : h₁ ≠ 0) {z : ℍ} (hz : (h₁ : ℍ → ℂ) z ≠ 0) :
    realizeOf Γ (quot g₁ h₁) z = (g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z :=
  ModularCurve.realizeOf_eq_div Γ hT g₁ h₁ (quot g₁ h₁) (quot_mul_eq hT g₁ h₁ hh₁) z hz

include hT in

theorem isBoundedUnder_realizeOf_quot {τ : ℍ} (hτ : (h₁ : ℍ → ℂ) τ ≠ 0) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Γ (quot g₁ h₁) z‖) := by
  have hh₁ : h₁ ≠ 0 := ne_zero_of_apply_ne_zero h₁ hτ
  have hcont : ContinuousAt (fun z : ℍ => (g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z) τ :=
    ((continuous_coe g₁).continuousAt).div ((continuous_coe h₁).continuousAt) hτ
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z‖) :=
    (hcont.norm.tendsto).isBoundedUnder_le
  obtain ⟨b, hb⟩ := hbd
  rw [Filter.eventually_map] at hb
  have hne : ∀ᶠ z in 𝓝 τ, (h₁ : ℍ → ℂ) z ≠ 0 :=
    ((continuous_coe h₁).continuousAt).eventually_ne hτ
  refine ⟨b, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [nhdsWithin_le_nhds hb, nhdsWithin_le_nhds hne] with z hz hz'
  rwa [realizeOf_quot_eq hT g₁ h₁ hh₁ hz']

include hT in

theorem not_isBoundedUnder_realizeOf_quot {τ' : ℍ} (hh₁ : h₁ ≠ 0)
    (hτ' : (h₁ : ℍ → ℂ) τ' = 0) (hg : (g₁ : ℍ → ℂ) τ' ≠ 0) :
    ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ') (fun z : ℍ => ‖realizeOf Γ (quot g₁ h₁) z‖) := by
  have hne : ∀ᶠ z in 𝓝[≠] τ', (h₁ : ℍ → ℂ) z ≠ 0 := eventually_ne_zero h₁ hh₁ τ'

  have hh0 : Tendsto (fun z : ℍ => ‖(h₁ : ℍ → ℂ) z‖) (𝓝[≠] τ') (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (((continuous_coe h₁).continuousAt (x := τ')).norm).tendsto
      rw [hτ', norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [hne] with z hz
      exact norm_pos_iff.mpr hz
  have hinv : Tendsto (fun z : ℍ => ‖(h₁ : ℍ → ℂ) z‖⁻¹) (𝓝[≠] τ') atTop :=
    tendsto_inv_nhdsGT_zero.comp hh0
  have hgt : Tendsto (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z‖) (𝓝[≠] τ') (𝓝 ‖(g₁ : ℍ → ℂ) τ'‖) :=
    (((continuous_coe g₁).continuousAt (x := τ')).norm).tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z‖ * ‖(h₁ : ℍ → ℂ) z‖⁻¹) (𝓝[≠] τ')
      atTop :=
    Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr hg) hgt hinv
  have hquot : Tendsto (fun z : ℍ => ‖realizeOf Γ (quot g₁ h₁) z‖) (𝓝[≠] τ') atTop := by
    refine hprod.congr' ?_
    filter_upwards [hne] with z hz
    rw [realizeOf_quot_eq hT g₁ h₁ hh₁ hz, norm_div, div_eq_mul_inv]
  exact not_isBoundedUnder_of_tendsto_atTop hquot

end Local

theorem pt_ne_pt_of_forall_smul_ne {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (τ τ' : ℍ) (hτ : ∀ γ ∈ CohCarrier.GammaH M H, γ • τ ≠ τ') :
    D.pt τ ≠ D.pt τ' := by
  intro hpt
  obtain ⟨k, g, h, hdet⟩ :=
    ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne M H τ τ' hτ
  obtain ⟨g₁, h₁, h₁τ, h₁τ', g₁τ'⟩ := exists_normalised_pair g h hdet
  have hh₁ : h₁ ≠ 0 := ne_zero_of_apply_ne_zero h₁ h₁τ

  have hmem : quot g₁ h₁ ∈ laurentBaseChange ℂ (xHFunctionField M H) :=
    ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H g₁ h₁ hh₁
  set x : laurentBaseChange ℂ (xHFunctionField M H) := ⟨quot g₁ h₁, hmem⟩ with hx
  have hxcoe : (x : LaurentSeries ℂ) = quot g₁ h₁ := rfl
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

  have hreg : x ∈ (D.pt τ).toValuationSubring := by
    rw [D.mem_pt_iff τ x, hxcoe]
    exact isBoundedUnder_realizeOf_quot hT g₁ h₁ h₁τ

  rw [hpt, D.mem_pt_iff τ' x, hxcoe] at hreg
  exact not_isBoundedUnder_realizeOf_quot hT g₁ h₁ hh₁ h₁τ' g₁τ' hreg

end ModularCurve.ComplexPlaceDictionaryOfOrbitH
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve.ComplexPlaceDictionaryOfOrbitH"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.ModularCurve.ComplexPlaceDictionaryOfOrbitH"

open ModularCurve.ComplexPlaceDictionaryOfOrbitH in
open scoped MatrixGroups in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (τ τ' : UpperHalfPlane) :
    D.pt τ = D.pt τ' ↔ ∃ γ ∈ CohCarrier.GammaH M H, γ • τ = τ' := by
  constructor
  · intro hpt
    by_contra hne
    push Not at hne
    exact pt_ne_pt_of_forall_smul_ne D τ τ' hne hpt
  · rintro ⟨γ, hγ, rfl⟩
    exact (D.pt_smul_of_mem hγ τ).symm

end S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH (solution)
