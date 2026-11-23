-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.notMem_rectBoundary_of_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.63808+00:00
-- url     : https://prove2.me/submissions/72615718-3ddb-4a51-8461-5366d77754aa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {p : ℂ}
    (hre : p.re ∈ Ioo (min z.re w.re) (max z.re w.re))
    (him : p.im ∈ Ioo (min z.im w.im) (max z.im w.im)) : p ∉ rectBoundary z w := by
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff, not_or, not_and]
  have key : ∀ {a b t : ℝ}, t ∈ Ioo (min a b) (max a b) → t ≠ a ∧ t ≠ b := by
    intro a b t ht
    obtain ⟨h1, h2⟩ := ht
    rw [min_lt_iff] at h1
    rw [lt_max_iff] at h2
    constructor <;> rintro rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  refine ⟨⟨⟨fun _ h ↦ (key him).1 h, fun _ h ↦ (key him).2 h⟩, fun h _ ↦ (key hre).1 h⟩,
    fun h _ ↦ (key hre).2 h⟩
end GroundTheory.Global.Elliptic
