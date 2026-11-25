-- Prove2me | solution 1 for GlobalTheory.Retract.surjective_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:10.997044+00:00
-- url     : https://prove2.me/submissions/a5cf21e9-a4a3-479d-bbd8-ea34c4a44688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_surjective_retraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y : Scheme.{u}} {i : X ⟶ Y} {r : Y ⟶ X} (hir : i ≫ r = 𝟙 X)
include hir
namespace GlobalTheory.Retract
theorem _root_.solution {T Z : Scheme.{u}} {t : T ⟶ X} {a : Z ⟶ Y} {r' : Z ⟶ T}
    (h : IsPullback a r' r t) : Surjective r' :=
  MorphismProperty.of_isPullback (P := @Surjective) h (surjective_retraction hir)
end GlobalTheory.Retract
