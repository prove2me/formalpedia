-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.iwAbs_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:32.94805+00:00
-- url     : https://prove2.me/submissions/dc80573f-cefa-4b6a-963d-5c0fcb8e1ec7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul

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
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
variable {δ K}
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution {k : G} (hk : k ∈ K) : iwAbs δ K k = 1 := by simpa using h.iwAbs_mul 1 hk
end GlobalTheory.Doubling.IsIwasawa
