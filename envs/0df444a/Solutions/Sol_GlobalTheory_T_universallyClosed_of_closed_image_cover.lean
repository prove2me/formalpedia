-- Prove2me | solution 1 for GlobalTheory.T.universallyClosed_of_closed_image_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:40.749861+00:00
-- url     : https://prove2.me/submissions/709fb190-67ca-4524-a2f0-da07b2345e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyClose
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyCloseStatement
import Theorems.Thm_GlobalTheory_universallyClosed_of_closed_cover_in_universallyClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y), UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) → π '' T = Set.univ → UniversallyClosed f := by
  first | exact @GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | exact GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | (intros; apply GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed <;> assumption)
end _root_.GlobalTheory.T
