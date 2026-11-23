-- Prove2me | solution 1 for GlobalTheory.SmGL.IsSubquotient.of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:39.138384+00:00
-- url     : https://prove2.me/submissions/c4c60066-e34d-419f-b5ed-2cd297451556

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
namespace IsSubquotient
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSubquotient σ ρ := by
  refine ⟨⊤, ⟨f.toLinearMap ∘ₗ (⊤ : Subrepresentation ρ).toSubmodule.subtype, fun g => ?_⟩, fun w => ?_⟩
  · ext v
    exact f.isIntertwining _ _ g v
  · obtain ⟨v, rfl⟩ := hf w
    exact ⟨⟨v, trivial⟩, rfl⟩
end IsSubquotient
end GlobalTheory.SmGL
