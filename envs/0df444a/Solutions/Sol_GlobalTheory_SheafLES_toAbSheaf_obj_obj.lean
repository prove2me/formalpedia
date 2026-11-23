-- Prove2me | solution 1 for GlobalTheory.SheafLES.toAbSheaf_obj_obj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:02.86269+00:00
-- url     : https://prove2.me/submissions/ad9b9414-b505-4fb2-bb30-d1e5a1d97f46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
open AlgebraicGeometry
variable (X : Scheme.{u})
variable {X}
namespace GlobalTheory.SheafLES
theorem _root_.solution (M : X.Modules) : ((toAbSheaf X).obj M).obj = M.presheaf := rfl
end GlobalTheory.SheafLES
