-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.vacuum_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:01.900069+00:00
-- url     : https://prove2.me/submissions/ea45bb0b-02ed-4955-9270-b23653a8a715

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_GlobalTheory_Phase_VacShape_ph_mul
import Theorems.Thm_GlobalTheory_Phase_VacShape_shape_at
import Theorems.Thm_GlobalTheory_Phase_VacShape_vac_smul
import Theorems.Thm_GlobalTheory_Phase_VacShape_pv_of_ph
import Theorems.Thm_GlobalTheory_Phase_isMu_one
import Theorems.Thm_GlobalTheory_Phase_ph_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, (∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧ ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0)) ∧ (PV φ → Shape φ) ∧ (∀ A ε, VacS A ε φ → ∃ u : ℂ, ‖u‖ = 1 ∧ PV (u • φ)) ∧ (PV φ → ∀ u : ℂ, Ph u → PV (u • φ)) ∧ ∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → Ph (φ a) → PV φ := by
  intro κ ι _ _ _ φ
  refine ⟨fun A ε h a ha => shape_at h a ha, ?_, fun A ε h => ?_, ?_,
    fun A ε h a ha hp => pv_of_ph h a ha hp⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩
    refine ⟨h.sb, ?_⟩
    by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
      refine ⟨φ a, a, S, f, hp a, hq, fun x => ?_⟩
      split_ifs with hS
      · exact (hx x).1 hS
      · exact (hx x).2 hS
    · push Not at h0
      exact ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩,
        fun x => by simp [h0]⟩
  · by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      have hn : ‖φ a‖ ≠ 0 := norm_ne_zero_iff.2 ha
      have e : ((((‖φ a‖ : ℝ) : ℂ) / φ a) • φ) a = ((‖φ a‖ : ℝ) : ℂ) := by
        rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha]
      refine ⟨((‖φ a‖ : ℝ) : ℂ) / φ a, by simp [hn], pv_of_ph (vac_smul h _) a ?_ ?_⟩
      · rw [e]; exact_mod_cast hn
      · rw [e]; exact ⟨1, one_pos, by simp⟩
    · push Not at h0
      exact ⟨1, norm_one, ⟨A, ε, vac_smul h _⟩, fun x => by simpa [h0] using ph_zero⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩ u hu
    exact ⟨⟨A, ε, vac_smul h _⟩, fun x => ph_mul hu (hp x)⟩
end GlobalTheory.Phase.VacShape
