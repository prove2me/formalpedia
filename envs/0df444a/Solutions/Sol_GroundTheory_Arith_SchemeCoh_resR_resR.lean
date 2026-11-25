-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resR_resR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:58.005729+00:00
-- url     : https://prove2.me/submissions/ba4de5be-9ac4-456b-bbac-5b18214e4d42

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X U) :
    resR i (resR h r) = resR (i.trans h) r := by
  rw [resR, resR, resR, ← RingHom.comp_apply, ← RingCat.hom_comp, ← Functor.map_comp]
  rfl
end GroundTheory.Arith.SchemeCoh
