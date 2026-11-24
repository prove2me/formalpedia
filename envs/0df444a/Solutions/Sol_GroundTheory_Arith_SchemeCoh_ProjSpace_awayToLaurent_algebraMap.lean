-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.awayToLaurent_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:39.487435+00:00
-- url     : https://prove2.me/submissions/b4721d7f-661d-4e7e-a06d-6f1ea236b9d0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {p : ℕ} (i : Fin p → Fin (n + 1)) (a : MvPolynomial (Fin (n + 1)) A) :
    awayToLaurent i (algebraMap _ _ a) = toLaurent A n a :=
  IsLocalization.lift_eq _ _
end GroundTheory.Arith.SchemeCoh.ProjSpace
