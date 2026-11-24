-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.coeff_toLaurent_expHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:43.437925+00:00
-- url     : https://prove2.me/submissions/747bac6d-7dbe-416c-83ca-c4172b6772bf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_expHom_injective

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
theorem _root_.solution (a : MvPolynomial (Fin (n + 1)) A) (e : Fin (n + 1) →₀ ℕ) :
    (toLaurent A n a).coeff (expHom n e) = a.coeff e :=
  Finsupp.mapDomain_apply expHom_injective _ _
end GroundTheory.Arith.SchemeCoh.ProjSpace
