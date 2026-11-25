-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.isFlat_flatSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:43.680104+00:00
-- url     : https://prove2.me/submissions/c491309d-4b4d-4f30-9211-fcd80d43287b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_flatSec_of_mem

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
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution (Φ : G → ℂ) (s₀ : ℂ) : IsFlat K (flatSec δ K Φ s₀) := fun s s' k hk => by
  rw [h.flatSec_of_mem _ _ _ hk, h.flatSec_of_mem _ _ _ hk]
end GlobalTheory.Doubling.IsIwasawa
