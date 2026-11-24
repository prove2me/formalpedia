-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.npow_iwAbs_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:25.098334+00:00
-- url     : https://prove2.me/submissions/3e01d20d-2ac6-46c0-baa8-7b406fec606d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_iwAbs_pos
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_left
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_right
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_continuous_iwAbs
import Theorems.Thm_GlobalTheory_Doubling_npow_mul
import Theorems.Thm_GlobalTheory_Doubling_continuous_npow
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
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) (t : ℂ) :
    (fun g => npow (iwAbs δ K g) t) ∈ indSpace δ K 1 t :=
  ⟨fun p g => by simp [h.iwAbs_left, npow_mul], continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos δ K) _,
    .of_invariant fun g k hk => by rw [h.iwAbs_right g hk]⟩
end GlobalTheory.Doubling.IsIwasawa
