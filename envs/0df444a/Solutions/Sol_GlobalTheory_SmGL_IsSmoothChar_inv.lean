-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSmoothChar.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:28.130037+00:00
-- url     : https://prove2.me/submissions/fb6879b0-5e8c-44a0-b598-9be18fd6fc31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff

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
namespace GlobalTheory.SmGL
namespace IsSmoothChar
theorem _root_.solution {χ : G →* Fˣ} (hχ : IsSmoothChar χ) : IsSmoothChar χ⁻¹ := by
  have : (χ⁻¹.ker : Set G) = χ.ker := by ext g; simp
  unfold IsSmoothChar; rw [this]; exact hχ
end IsSmoothChar
end GlobalTheory.SmGL
