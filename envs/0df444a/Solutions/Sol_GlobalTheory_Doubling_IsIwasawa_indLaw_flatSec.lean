-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.indLaw_flatSec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:35.047559+00:00
-- url     : https://prove2.me/submissions/187289a8-783a-4fab-9d2e-9fac2587d672

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_hom_pos
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_left
import Theorems.Thm_GlobalTheory_Doubling_npow_mul
import Theorems.Thm_GlobalTheory_Doubling_npow_add

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
theorem _root_.solution {Φ : G → ℂ} {ρ s₀ : ℂ} (hΦ : IndLaw δ χ (s₀ + ρ) Φ) (s : ℂ) :
    IndLaw δ χ (s + ρ) (flatSec δ K Φ s₀ s) := fun p g => by
  rw [flatSec, flatSec, hΦ, h.iwAbs_left, npow_mul, show s + ρ = (s₀ + ρ) + (s - s₀) by ring,
    npow_add (hom_pos δ p) _ (s - s₀)]
  ring
end GlobalTheory.Doubling.IsIwasawa
