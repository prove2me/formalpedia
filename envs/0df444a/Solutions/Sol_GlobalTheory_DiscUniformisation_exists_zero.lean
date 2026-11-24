-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.exists_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:49.987358+00:00
-- url     : https://prove2.me/submissions/4d6e5901-97ef-4553-bb1d-c92307651cd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
import Theorems.Thm_GlobalTheory_DiscUniformisation_tendsto_coeff_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (F : ModularForm 𝒮ℒ 12) (c : ℂ) (hc : c ≠ 0)
    (hF : Tendsto F atImInfty (𝓝 c)) : ∃ z, F z = 0 := by
  by_contra hne
  push_neg at hne

  have hD0 : Tendsto ModularForm.discriminant atImInfty (𝓝 0) := by
    have h1 := tendsto_coeff_zero (ModularFormClass.modularForm CuspForm.discriminant)
    rw [ModularFormClass.coe_modularForm,
      CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL,
      CuspForm.coe_discriminant] at h1
    exact h1
  have hG0 : Tendsto (fun τ => ModularForm.discriminant τ / F τ) atImInfty (𝓝 0) := by
    have h := hD0.div hF hc
    rw [zero_div] at h
    exact h

  let G0 : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => ModularForm.discriminant τ / F τ
      slash_action_eq' := by
        rintro γ ⟨g, rfl⟩
        funext τ
        have key : SlashAction.map (0 : ℤ) g (fun τ => ModularForm.discriminant τ / F τ) τ =
            ModularForm.discriminant τ / F τ := by
          rw [ModularForm.slash_action_eq'_iff, zpow_zero, one_mul]
          have hΔ := (ModularForm.slash_action_eq'_iff 12 (⇑CuspForm.discriminant) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ ⟨g, rfl⟩) τ)
          have hF' := (ModularForm.slash_action_eq'_iff 12 (⇑F) g τ).1
            (congrFun (SlashInvariantForm.slash_action_eqn F _ ⟨g, rfl⟩) τ)
          rw [CuspForm.coe_discriminant] at hΔ
          show ModularForm.discriminant (g • τ) / F (g • τ) = ModularForm.discriminant τ / F τ
          have hd : ∀ x : ℂ, ModularForm.discriminant (g • τ) = x * ModularForm.discriminant τ → x ≠ 0 := by
            rintro x hx rfl
            rw [zero_mul] at hx
            exact ModularForm.discriminant_ne_zero _ hx
          have hx0 := hd _ hΔ
          rw [hΔ, hF']
          rw [mul_div_mul_left _ _ hx0]
        exact key }
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty G0.toFun :=
    UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty hG0
  let G : ModularForm 𝒮ℒ 0 :=
    { toSlashInvariantForm := G0
      holo' := (ModularFormClass.holo CuspForm.discriminant).div (ModularFormClass.holo F) hne
      bdd_at_cusps' := by
        intro c' hc'
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
        intro γ _
        convert hbdd using 1
        exact G0.slash_action_eq' _ ⟨γ, rfl⟩ }
  obtain ⟨c', hc'⟩ := ModularForm.eq_const_of_weight_zero G
  have hGt : Tendsto (⇑G) atImInfty (𝓝 0) := hG0
  rw [hc'] at hGt
  have hc0 : c' = 0 := tendsto_nhds_unique tendsto_const_nhds hGt
  have h1 : G UpperHalfPlane.I = 0 := by rw [hc', Function.const_apply, hc0]
  have h2 : ModularForm.discriminant UpperHalfPlane.I / F UpperHalfPlane.I = 0 := h1
  rcases div_eq_zero_iff.1 h2 with h3 | h3
  · exact ModularForm.discriminant_ne_zero _ h3
  · exact hne _ h3
end GlobalTheory.DiscUniformisation
