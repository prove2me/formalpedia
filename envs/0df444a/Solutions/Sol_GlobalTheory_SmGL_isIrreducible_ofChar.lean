-- Prove2me | solution 1 for GlobalTheory.SmGL.isIrreducible_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:10.110866+00:00
-- url     : https://prove2.me/submissions/c47860fe-412f-46c1-b3c0-3ae4cf2df38c

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
theorem _root_.solution (χ : G →* Fˣ) : (ofChar χ).IsIrreducible := by
  have : Nontrivial (Subrepresentation (ofChar χ)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule F F) this⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)
end GlobalTheory.SmGL
