-- Prove2me | solution 1 for GlobalTheory.SmGL.jacquet_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:16.216901+00:00
-- url     : https://prove2.me/submissions/8e0f7491-59cb-4ace-af8c-c19559d00785

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
namespace GlobalTheory.SmGL
theorem _root_.solution (ρ : Representation F G V) (N : Subgroup G) (s : H →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (m : H) (v : V) :
    jacquet ρ N s hs m (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (s m) v) := rfl
end GlobalTheory.SmGL
