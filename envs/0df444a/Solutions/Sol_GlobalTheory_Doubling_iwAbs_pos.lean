-- Prove2me | solution 1 for GlobalTheory.Doubling.iwAbs_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:30.979543+00:00
-- url     : https://prove2.me/submissions/3f216c4c-55a2-48dc-ae1f-7e354b7347d6

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_hom_pos

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
namespace GlobalTheory.Doubling
theorem _root_.solution (g : G) : 0 < iwAbs δ K g := by
  unfold iwAbs; split_ifs
  · exact hom_pos δ _
  · exact one_pos
end GlobalTheory.Doubling
