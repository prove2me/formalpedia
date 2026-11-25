-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:39.375796+00:00
-- url     : https://prove2.me/submissions/183f779c-74fa-483e-849b-462d238a9b8b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_residueField
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_residueField

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
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) :=
  hasProjectiveDimensionLT_of_residueField d (hasProjectiveDimensionLT_residueField hd) M
end GroundTheory.Arith.SchemeCoh
