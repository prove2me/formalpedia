-- Prove2me | solution 1 for GroundTheory.LocalField.CongrData.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:12:16.10784+00:00
-- url     : https://prove2.me/submissions/61837fa5-0175-48ba-bc87-557816ce6f14

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal

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
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
omit [Fintype G]
namespace GroundTheory.LocalField
namespace CongrData
theorem _root_.solution {f : G → ℂ} (hf : CongrData ζ N s a f) (x : Algebra.adjoin ℤ ({ζ} : Set ℂ)) :
    CongrData ζ N s a ((x : ℂ) • f) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  refine ⟨ι, inferInstance, fun i ↦ x * c i, β, β', hβ, ?_, ?_⟩
  · simp [h1, Finset.mul_sum, mul_assoc]
  · simp [h2, Finset.mul_sum, mul_assoc]
end CongrData
end GroundTheory.LocalField
