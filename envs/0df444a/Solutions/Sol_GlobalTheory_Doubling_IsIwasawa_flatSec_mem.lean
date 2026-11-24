-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.flatSec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:23.72668+00:00
-- url     : https://prove2.me/submissions/d59dc814-95fd-4eae-ac7c-3a9862372a68

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_iwAbs_pos
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_right
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_continuous_iwAbs
import Theorems.Thm_GlobalTheory_Doubling_continuous_npow
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_indLaw_flatSec

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) {Φ : G → ℂ}
    {ρ s₀ : ℂ} (hΦ : Φ ∈ indSpace δ K χ (s₀ + ρ)) (s : ℂ) : flatSec δ K Φ s₀ s ∈ indSpace δ K χ (s + ρ) :=
  ⟨h.indLaw_flatSec hΦ.1 s, hΦ.2.1.mul (continuous_npow (h.continuous_iwAbs hP hδ hK) (iwAbs_pos δ K) _),
    hΦ.2.2.mul_invariant (f := fun g => npow (iwAbs δ K g) (s - s₀)) fun g k hk => by rw [h.iwAbs_right g hk]⟩
end GlobalTheory.Doubling.IsIwasawa
