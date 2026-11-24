-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.bump_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:48.130811+00:00
-- url     : https://prove2.me/submissions/b3580ed1-2aef-4e9a-aec1-4d277b29828d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_eq_mul_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] {g₀ g₁ : V → ℂ} (h₀ : Bump g₀) (h₁ : Bump g₁) : ∃ s : ℝ, 0 < s ∧ ∀ m : (V → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ ∈ SB V, ∀ a : V, m (fun x => φ (x + a)) = m φ) → m g₀ = s * m g₁ ∧ (m g₀ = 0 → ∀ g ∈ SB V, m g = 0) := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have pos : ∀ g : V → ℂ, Bump g → ∃ s : ℝ, 0 < s ∧ ∫ x, g x ∂μ = s := fun g hg => by
    refine ⟨∫ x, (g x).re ∂μ, ?_, ?_⟩
    · refine (Complex.continuous_re.comp hg.1.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hg.1.2.comp_left (g := Complex.re) rfl) (fun x => ?_) (x := 0) (by simp [hg.2.2])
      rcases hg.2.1 x with h | h <;> simp [h]
    · rw [← integral_complex_ofReal]
      congr 1; ext x; rcases hg.2.1 x with h | h <;> simp [h]
  obtain ⟨a, ha, ea⟩ := pos _ h₀
  obtain ⟨b, hb, eb⟩ := pos _ h₁
  refine ⟨a / b, div_pos ha hb, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := HaarUniq.exists_eq_mul_integral V μ m hm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ h₀.1, hc _ h₁.1, ea, eb]
  refine ⟨by push_cast; field_simp, fun h g hg => ?_⟩
  rw [hc g hg, (mul_eq_zero.1 h).resolve_right ha', zero_mul]
end GlobalTheory.ThK.Dbl.LD
