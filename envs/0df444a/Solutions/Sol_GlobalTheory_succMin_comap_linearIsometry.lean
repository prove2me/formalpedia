-- Prove2me | solution 1 for GlobalTheory.succMin_comap_linearIsometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:09.962383+00:00
-- url     : https://prove2.me/submissions/11cdc510-e80b-4dc7-9f7f-7ad185dd990e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMin_map_linearIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution (f : F →ₗᵢ[ℝ] E) (h : (L : Set E) ⊆ Set.range f) (i : ℕ) :
    succMin (ZLattice.comap ℝ L f.toLinearMap) i = succMin L i := by
  rw [← succMin_map_linearIsometry f, ZLattice.comap, Submodule.map_comap_eq_self]
  exact fun x hx => h hx
end GlobalTheory
