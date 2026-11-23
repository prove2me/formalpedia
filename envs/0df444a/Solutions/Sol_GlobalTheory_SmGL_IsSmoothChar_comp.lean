-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSmoothChar.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:41.072336+00:00
-- url     : https://prove2.me/submissions/6ed9c58c-022e-4389-98af-564dd05ffed9

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
theorem _root_.solution [TopologicalSpace H] {χ : G →* Fˣ} (hχ : IsSmoothChar χ) (s : H →* G)
    (hs : Continuous s) : IsSmoothChar (χ.comp s) :=
  IsOpen.preimage hs hχ
end IsSmoothChar
end GlobalTheory.SmGL
