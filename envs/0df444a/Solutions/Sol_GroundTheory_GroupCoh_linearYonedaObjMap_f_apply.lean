-- Prove2me | solution 1 for GroundTheory.GroupCoh.linearYonedaObjMap_f_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:10.988563+00:00
-- url     : https://prove2.me/submissions/384bffc8-c0de-4f38-957d-33802f816c87

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
namespace GroundTheory.GroupCoh
theorem _root_.solution {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) (n : ℕ)
    (x : Y.X n ⟶ B) : (linearYonedaObjMap (R := R) f B).f n x = f.f n ≫ x := rfl
end GroundTheory.GroupCoh
