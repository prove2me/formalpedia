-- Prove2me | solution 1 for GlobalTheory.Doubling.flatSec_flatSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:59.002893+00:00
-- url     : https://prove2.me/submissions/c444a5bf-b87a-4e20-87a8-17e18d7ed965

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_iwAbs_pos
import Theorems.Thm_GlobalTheory_Doubling_npow_add
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self

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
theorem _root_.solution (Φ : G → ℂ) (s₀ s₁ s : ℂ) : flatSec δ K (flatSec δ K Φ s₀ s₁) s₁ s = flatSec δ K Φ s₀ s :=
  funext fun g => by
    simp only [flatSec, mul_assoc, ← npow_add (iwAbs_pos δ K g)]
    congr 2; ring
end GlobalTheory.Doubling
