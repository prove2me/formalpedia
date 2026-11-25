-- Prove2me | solution 1 for GlobalTheory.Doubling.IsRightSmooth.mem_indSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:06.04995+00:00
-- url     : https://prove2.me/submissions/44daa751-e6e6-4205-bdeb-eda5345ab5c6

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_isKFinite

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
namespace IsRightSmooth
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ)
    (hK : IsCompact (K : Set G)) (hl : IndLaw δ χ t Φ) : Φ ∈ indSpace δ K χ t := ⟨hl, h.continuous, h.isKFinite hK⟩
end IsRightSmooth
end GlobalTheory.Doubling
