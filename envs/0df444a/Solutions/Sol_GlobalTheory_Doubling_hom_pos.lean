-- Prove2me | solution 1 for GlobalTheory.Doubling.hom_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:44.008907+00:00
-- url     : https://prove2.me/submissions/d9151f26-b87e-4a97-a8b3-750a00a739e9

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
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
namespace GlobalTheory.Doubling
theorem _root_.solution {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p :=
  pos_iff_ne_zero.2 ((Group.isUnit p).map δ).ne_zero
end GlobalTheory.Doubling
