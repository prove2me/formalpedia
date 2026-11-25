-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_indSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:19.045784+00:00
-- url     : https://prove2.me/submissions/c8f9bf34-c497-4a01-a838-a114ec89b6e8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

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
theorem _root_.solution [TopologicalSpace G] {Φ : G → ℂ} :
    Φ ∈ indSpace δ K χ t ↔ IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ := Iff.rfl
end GlobalTheory.Doubling
