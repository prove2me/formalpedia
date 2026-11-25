-- Prove2me | solution 1 for GlobalTheory.T.unramified_quadratic_norm_trace_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:23:58.089462+00:00
-- url     : https://prove2.me/submissions/2fd50504-10f8-44dd-bbeb-17e3f66126f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticUniformizerTraceNorm
import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticUniformizerTraceNormStatement
import Theorems.Thm_GlobalTheory_unramified_quadratic_uniformizer_trace_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex K L = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  first | exact @GlobalTheory.unramified_quadratic_uniformizer_trace_norm | exact GlobalTheory.unramified_quadratic_uniformizer_trace_norm | (intros; apply GlobalTheory.unramified_quadratic_uniformizer_trace_norm <;> assumption)
end _root_.GlobalTheory.T
