-- Prove2me | solution 1 for GlobalTheory.SmGL.twist_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:55.084015+00:00
-- url     : https://prove2.me/submissions/4b198148-bb3a-4fce-a9a2-835755c9ddc6

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
theorem _root_.solution (ρ : Representation F G V) (χ ψ : G →* Fˣ) :
    twist (twist ρ χ) ψ = twist ρ (ψ * χ) := by
  ext g v; simp [smul_smul]
end GlobalTheory.SmGL
