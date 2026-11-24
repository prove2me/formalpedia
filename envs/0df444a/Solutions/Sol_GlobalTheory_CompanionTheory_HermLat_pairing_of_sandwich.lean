-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:35.41335+00:00
-- url     : https://prove2.me/submissions/b4f3dcdd-2067-4139-a0a2-aa5ec46b1eee

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_smul_mem_of_isLat
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_exists_smul_mem_of_isLat
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_pairing_le
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_adjoin_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution : StSandwich → StPairing := by
  intro hS L _ _ _ _ s hs δ hδ V _ _ _ h hh Λ hΛ
  obtain ⟨hL, hint, hmax⟩ := hΛ
  refine ⟨fun x hx y hy => pairing_le hδ hh hL hint hx hy, ?_⟩
  intro p hp hunif x hx hxp hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 by norm_num)
    have := hunif a ha
    rw [norm_zero] at this
    linarith
  have hδ0 : δ ≠ 0 := hδ.1
  have hδn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  by_cases hex : ∃ y ∈ Λ, ‖h x y‖ = ‖δ‖
  · obtain ⟨y, hy, hyn⟩ := hex
    have hne : h x y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyn
      exact hδ0 (norm_eq_zero.mp hyn.symm)
    refine ⟨(δ / h x y) • y, smul_mem_of_isLat hL ?_ hy, ?_⟩
    · rw [norm_div, hyn, div_self hδn.ne']
    · rw [hh.2.1]
      field_simp
  · exfalso
    have hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖ := by
      intro y hy
      have hlt : ‖h x y‖ < ‖δ‖ :=
        lt_of_le_of_ne (pairing_le hδ hh hL hint hx hy) fun e => hex ⟨y, hy, e⟩
      have h2 : ‖h x y / δ‖ < 1 := by
        rw [norm_div, div_lt_one hδn]
        exact hlt
      have h3 := hunif _ h2
      rw [norm_div, div_le_iff₀ hδn] at h3
      exact h3
    have hle : Λ ≤ adjoin L Λ (p⁻¹ • x) := fun l hl => ⟨l, hl, 0, by simp, by simp⟩
    have hL' : IsLat L (adjoin L Λ (p⁻¹ • x)) := by
      refine hS L V Λ _ p hL hp0 ?_ ?_ ?_
      · rintro _ ⟨l, hl, a, ha, rfl⟩
        have e : p • (l + a • p⁻¹ • x) = p • l + a • x := by
          rw [smul_add, smul_comm p a, smul_smul p, mul_inv_cancel₀ hp0, one_smul]
        rw [e]
        exact Λ.add_mem (smul_mem_of_isLat hL hp.le hl) (smul_mem_of_isLat hL ha hx)
      · intro v
        obtain ⟨a, ha, hav⟩ := exists_smul_mem_of_isLat hL v
        exact ⟨a, ha, hle hav⟩
      · rintro b hb _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨b • l, smul_mem_of_isLat hL hb hl, b * a, ?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_one₀ hb (norm_nonneg _) ha
        · rw [smul_add, smul_smul]
    have heq := hmax _ hL' (adjoin_integral hs hδ hh hint hp0 hq hsmall) hle
    apply hxp
    rw [← heq]
    exact ⟨0, Λ.zero_mem, 1, by simp, by simp⟩
end GlobalTheory.CompanionTheory.HermLat
