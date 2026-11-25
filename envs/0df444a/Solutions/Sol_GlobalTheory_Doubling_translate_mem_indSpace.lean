-- Prove2me | solution 1 for GlobalTheory.Doubling.translate_mem_indSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:19.422792+00:00
-- url     : https://prove2.me/submissions/6dd63f77-ba88-4322-9da9-f30f95d300a2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsKFinite_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}
variable (K)
variable {δ K χ t}
namespace GlobalTheory.Doubling
theorem _root_.solution [TopologicalSpace G] [ContinuousMul G] {Φ : G → ℂ} (h : Φ ∈ indSpace δ K χ t) {k : G}
    (hk : k ∈ K) : (fun g => Φ (g * k)) ∈ indSpace δ K χ t :=
  ⟨fun p g => by simpa only [mul_assoc] using h.1 p (g * k), h.2.1.comp (continuous_mul_const k), h.2.2.translate hk⟩
end GlobalTheory.Doubling
