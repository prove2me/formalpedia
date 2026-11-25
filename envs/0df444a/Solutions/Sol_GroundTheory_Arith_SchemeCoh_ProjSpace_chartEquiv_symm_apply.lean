-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.chartEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:13.684463+00:00
-- url     : https://prove2.me/submissions/4a244627-24fa-4bd9-a1aa-4da39995aea1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange

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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
variable {A B n}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    (chartEquiv A j).symm p = polyToChart A j p := rfl
end GroundTheory.Arith.SchemeCoh.ProjSpace
