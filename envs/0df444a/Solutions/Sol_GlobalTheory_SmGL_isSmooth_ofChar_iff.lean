-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_ofChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:17.831251+00:00
-- url     : https://prove2.me/submissions/639d703f-5a1a-4489-bcda-a6a96d936790

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
theorem _root_.solution (χ : G →* Fˣ) : IsSmooth (ofChar χ) ↔ IsSmoothChar χ := by
  refine ⟨fun h => ?_, fun h => isSmooth_twist (fun v => by simp) h⟩
  have : (χ.ker : Set G) = {g | ofChar χ g 1 = 1} := by ext g; simp
  unfold IsSmoothChar; rw [this]; exact h 1
end GlobalTheory.SmGL
