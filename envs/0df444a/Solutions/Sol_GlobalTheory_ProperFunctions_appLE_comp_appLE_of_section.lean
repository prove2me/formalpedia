-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.appLE_comp_appLE_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:34.31018+00:00
-- url     : https://prove2.me/submissions/e6baad8e-2de0-4ab5-a7db-ed735e3fa37c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (U : X.Opens)
    (W : S.Opens) (hW : W ≤ e ⁻¹ᵁ U) :
    p.appLE ⊤ U (le_preimage_top p U) ≫ e.appLE U W hW =
      Scheme.Hom.appLE (𝟙 S) ⊤ W (le_preimage_top _ W) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  congr 1
end GlobalTheory.ProperFunctions
