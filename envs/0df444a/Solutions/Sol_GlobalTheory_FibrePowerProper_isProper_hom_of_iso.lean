-- Prove2me | solution 1 for GlobalTheory.FibrePowerProper.isProper_hom_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:49.707924+00:00
-- url     : https://prove2.me/submissions/e282634f-60cb-49b2-ab75-e5810696848b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper
namespace GlobalTheory.FibrePowerProper
theorem _root_.solution {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by
  have hw : X.hom = e.hom.left ≫ Y.hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [hw]
  infer_instance
end GlobalTheory.FibrePowerProper
