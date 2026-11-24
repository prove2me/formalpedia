-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.iwAbs_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:25.369801+00:00
-- url     : https://prove2.me/submissions/9cf91541-de0c-4ffa-a911-1dc5404b8744

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
theorem _root_.solution (g : G) {k : G} (hk : k ∈ K) : iwAbs δ K (g * k) = iwAbs δ K g := by
  obtain ⟨p', k', hk', rfl⟩ := h.1 g
  rw [mul_assoc, h.iwAbs_mul _ (mul_mem hk' hk), h.iwAbs_mul _ hk']
end GlobalTheory.Doubling.IsIwasawa
