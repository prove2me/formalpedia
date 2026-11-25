-- Prove2me | solution 1 for GlobalTheory.HTLat.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:34.631903+00:00
-- url     : https://prove2.me/submissions/0a8a95de-7f27-41cc-9f22-9f4de62c3d95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
variable (v : Valuation C ℝ≥0)
variable {v}
namespace GlobalTheory.HTLat
theorem _root_.solution (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) {x : U}
    (h₁ : La ≤ (Submodule.span C {x}).restrictScalars O) (h₂ : La ≠ ⊥) :
    ∃ c : C, c ≠ 0 ∧ La = Submodule.span O {c • x} := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have h3 : ∀ y ∈ s, ∃ c : C, c • x = y := fun y hy =>
    Submodule.mem_span_singleton.1 (h₁ (Submodule.subset_span hy))
  choose! c hc using h3
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h₂
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image (fun y => v (c y)) hs
  have hle : Submodule.span O (s : Set U) ≤ Submodule.span O {c y • x} := by
    rw [Submodule.span_le]
    intro z hz
    by_cases h0 : c y = 0
    · have : c z = 0 := by simpa [h0] using hmax z hz
      rw [← hc z hz, this, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨b, hb⟩ := hv.exists_of_le_one (r := c z / c y) (by
        rw [map_div₀]; exact div_le_one_of_le₀ (hmax z hz) zero_le)
      refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
      rw [← algebraMap_smul C b, hb, smul_smul, div_mul_cancel₀ _ h0, hc z hz]
  refine ⟨c y, fun h0 => h₂ ?_, le_antisymm hle ?_⟩
  · rw [h0, zero_smul, Submodule.span_zero_singleton] at hle
    exact le_bot_iff.1 hle
  · rw [hc y hy]
    exact Submodule.span_mono (by simpa using hy)
end GlobalTheory.HTLat
