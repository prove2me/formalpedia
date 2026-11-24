-- Prove2me | solution 1 for GlobalTheory.haar_lintegral_mul_right_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:04.018834+00:00
-- url     : https://prove2.me/submissions/a612f6e1-70c3-4cac-a08d-dff429696a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
import Theorems.Thm_GlobalTheory_HaarRightTranslate_map_mul_right_eq_modular
import Theorems.Thm_GlobalTheory_HaarRightTranslate_modular_bdd_on_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
      [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H),
      μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal,
        Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨M, hM⟩ := HaarRightTranslate.modular_bdd_on_compact hK
  refine ⟨M, fun y hy φ hφ => ?_⟩
  have e : ∫⁻ x, φ (x * y) ∂μ = ∫⁻ x, φ x ∂(map (· * y) μ) :=
    (lintegral_map hφ (measurable_mul_const y)).symm
  rw [e, HaarRightTranslate.map_mul_right_eq_modular μ y, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul]
  gcongr
  exact_mod_cast hM y hy
end GlobalTheory
