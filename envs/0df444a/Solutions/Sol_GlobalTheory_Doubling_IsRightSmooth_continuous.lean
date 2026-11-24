-- Prove2me | solution 1 for GlobalTheory.Doubling.IsRightSmooth.continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:31.881538+00:00
-- url     : https://prove2.me/submissions/7687b2f8-7c13-4c09-b8ce-1b861db9f6db

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
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
namespace GlobalTheory.Doubling
namespace IsRightSmooth
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ) :
    Continuous Φ := by
  obtain ⟨U, hU, h⟩ := h
  refine continuous_iff_continuousAt.2 fun x => (continuousAt_const (y := Φ x)).congr ?_
  filter_upwards [(hU.preimage (continuous_const_mul x⁻¹)).mem_nhds (x := x) (by simp)] with y hy
  rw [← h x _ hy, mul_inv_cancel_left]
end IsRightSmooth
end GlobalTheory.Doubling
