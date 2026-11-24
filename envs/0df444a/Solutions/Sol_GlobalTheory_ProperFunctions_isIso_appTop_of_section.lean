-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:49.11768+00:00
-- url     : https://prove2.me/submissions/e0a50974-4126-40a8-9730-71cab0e0250f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_section_of_fiber

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
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [GeometricallyIntegral p] {e : S ⟶ X} (he : e ≫ p = 𝟙 S) :
    IsIso p.appTop := by
  refine isIso_appTop_of_section_of_fiber p (fun s ↦ ?_) he
  have : UniversallyClosed (p.fiberToSpecResidueField s) :=
    inferInstanceAs (UniversallyClosed (pullback.snd p (S.fromSpecResidueField s)))
  have := isIso_appTop_of_field (k := S.residueField s) (p.fiberToSpecResidueField s)
  exact (ConcreteCategory.bijective_of_isIso _).2
end GlobalTheory.ProperFunctions
