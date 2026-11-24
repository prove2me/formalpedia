-- Prove2me | solution 1 for GlobalTheory.Doubling.isIwasawa_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:40.407347+00:00
-- url     : https://prove2.me/submissions/15717ea3-ab84-44a7-9cdb-66571413f41d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_triv_of_isCompact

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
omit [IsTopologicalGroup G]
namespace GlobalTheory.Doubling
theorem _root_.solution (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : IsIwasawa δ K := ⟨h, triv_of_isCompact hP hδ hK⟩
end GlobalTheory.Doubling
