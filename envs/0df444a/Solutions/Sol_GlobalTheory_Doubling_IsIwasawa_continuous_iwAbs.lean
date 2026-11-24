-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.continuous_iwAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:43:03.653206+00:00
-- url     : https://prove2.me/submissions/0143be37-73dc-4d05-89a0-95b9fae77aca

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul
import Theorems.Thm_GlobalTheory_Doubling_continuous_of_prod

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.Doubling
namespace IsIwasawa
theorem _root_.solution (h : IsIwasawa δ K) (hP : IsClosed (P : Set G)) (hδ : Continuous δ)
    (hK : IsCompact (K : Set G)) : Continuous (iwAbs δ K) :=
  continuous_of_prod hP hK h.1 ((hδ.comp continuous_fst).congr fun x => (h.iwAbs_mul x.1 x.2.2).symm)
end IsIwasawa
end GlobalTheory.Doubling
