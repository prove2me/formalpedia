-- Prove2me | solution 1 for GlobalTheory.GraphClosureExample.isFinite_str
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:54.89629+00:00
-- url     : https://prove2.me/submissions/591c3f89-1e56-4236-a603-b0f2c151410d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
open GlobalTheory.GraphClosureExample
namespace GlobalTheory.GraphClosureExample
theorem _root_.solution (d : ℤ) : IsFinite (str d) := by
  rw [IsFinite.SpecMap_iff]
  refine RingHom.finite_algebraMap.mpr ⟨⟨{1, Zsqrtd.sqrtd}, ?_⟩⟩
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have : (⟨a, b⟩ : ℤ√d) = a • 1 + b • Zsqrtd.sqrtd := by ext <;> simp
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
end GlobalTheory.GraphClosureExample
