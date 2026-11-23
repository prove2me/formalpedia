-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_smoothRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:19.729951+00:00
-- url     : https://prove2.me/submissions/5cba082e-8267-4d68-aab7-ab237eb6533b

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
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
theorem _root_.solution (ρ : Representation F G V) : IsSmooth (smoothRep ρ) := fun v => by
  have : {g : G | smoothRep ρ g v = v} = {g : G | ρ g v = v} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact v.2
end GlobalTheory.SmGL
