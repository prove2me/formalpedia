-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.goodAcyclic_modulesAb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:19.477842+00:00
-- url     : https://prove2.me/submissions/12831b53-085b-4422-ab1c-49c7150554d9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_isBasicCover

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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (F : X.Modules) [F.IsQuasicoherent] :
    GoodAcyclic (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U)
      (modulesAb F) :=
  fun _ _ _ _ _ hU => cechAcyclic_of_isBasicCover F hU
end GroundTheory.Arith.SchemeCoh
