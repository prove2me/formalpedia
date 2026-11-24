-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.pv_of_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:39.930225+00:00
-- url     : https://prove2.me/submissions/12fdd9bf-7495-4e60-871b-d30fd2978871

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_GlobalTheory_Phase_VacShape_ph_mul
import Theorems.Thm_GlobalTheory_Phase_VacShape_ph_of_isMu
import Theorems.Thm_GlobalTheory_Phase_VacShape_shape_at
import Theorems.Thm_GlobalTheory_Phase_ph_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) (hp : Ph (φ a)) : PV φ := by
  refine ⟨⟨A, ε, h⟩, fun x => ?_⟩
  obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
  by_cases hS : x - a ∈ S
  · rw [(hx x).1 hS]; exact ph_mul hp (ph_of_isMu (hq.1 _ hS))
  · rw [(hx x).2 hS]; exact ph_zero
end GlobalTheory.Phase.VacShape
