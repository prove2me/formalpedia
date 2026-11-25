-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.premises_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:42.497654+00:00
-- url     : https://prove2.me/submissions/871810c4-179a-4a4e-9fb4-0184b730347d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
import Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_symm
import Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_balanced
import Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_posDef
import Theorems.Thm_GlobalTheory_LatticeBoundTests_exists_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (cj : E → E) (w : 𝓞 E) (Y : Type)
      (_ : AddCommGroup Y) (_ : Module (𝓞 E) Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y)
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ),
      (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ (∃ z, cj z ≠ z) ∧
      (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) ∧ (w : E) + cj w = 1 ∧
      0 < Module.finrank ℤ Y ∧ (∀ x y, β x y = β y x) ∧
      (∀ c c' : 𝓞 E, (c' : E) = cj c → ∀ x y, β (c • x) y = β x (c' • y)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => β (b i) (b j)).PosDef := by
  obtain ⟨w, hw⟩ := exists_half
  refine ⟨K₃, inferInstance, inferInstance, fun z => IsCMField.complexConj K₃ z, w, 𝓞 K₃,
    inferInstance, inferInstance, inferInstance, inferInstance, trBil K₃,
    fun φ z => IsCMField.complexEmbedding_complexConj K₃ φ z, ?_,
    fun c => ⟨IsCMField.ringOfIntegersComplexConj K₃ c,
      IsCMField.coe_ringOfIntegersComplexConj K₃ c⟩, hw, Module.finrank_pos, trBil_symm K₃,
    trBil_balanced K₃, _, inferInstance, RingOfIntegers.basis K₃, trBil_posDef K₃⟩
  by_contra h
  push_neg at h
  exact IsCMField.complexConj_ne_one K₃ (AlgEquiv.ext h)
end GlobalTheory.LatticeBoundTests
