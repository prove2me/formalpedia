-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.exists_isUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:45.817523+00:00
-- url     : https://prove2.me/submissions/252fde8a-b817-43ce-859f-ca16a6466862

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsUniformizerNonarchimedean
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  have hyn : 0 < ‖p‖⁻¹ ^ n := zpow_pos (inv_pos.mpr hp0) n
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']
end GlobalTheory.CompanionTheory.CartGL
