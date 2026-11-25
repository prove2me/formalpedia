-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_iff_isSmoothRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:39.457046+00:00
-- url     : https://prove2.me/submissions/372e7232-da26-4a49-a82b-35664ac7c9dc

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
theorem _root_.solution {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) :
    IsSmooth ρ ↔ IsSmoothRep ρ := Iff.rfl
end GlobalTheory.SmGL
