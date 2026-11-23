-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:54.7561+00:00
-- url     : https://prove2.me/submissions/240e3c24-c63b-4b7f-a0ef-d7b0762194db

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
theorem _root_.solution [TopologicalSpace H] {ρ : Representation F G V} (hρ : IsSmooth ρ) (s : H →* G)
    (hs : Continuous s) : IsSmooth (ρ.comp s : Representation F H V) :=
  fun v => (hρ v).preimage hs
end GlobalTheory.SmGL
