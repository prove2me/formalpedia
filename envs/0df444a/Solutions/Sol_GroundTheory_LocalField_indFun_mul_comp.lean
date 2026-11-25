-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_mul_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:47.542689+00:00
-- url     : https://prove2.me/submissions/a2be3c61-844d-4c9c-8ff5-58dbe1910289

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]
namespace GroundTheory.LocalField
theorem _root_.solution (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    indFun φ (ψ * (χ ∘ φ)) = indFun φ ψ * χ := by
  classical
  funext s
  simp only [indFun_apply, Pi.mul_apply, Function.comp_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  split_ifs with hh
  · rw [hh]
    congr 1
    simpa using hχ s t⁻¹
  · simp
end GroundTheory.LocalField
