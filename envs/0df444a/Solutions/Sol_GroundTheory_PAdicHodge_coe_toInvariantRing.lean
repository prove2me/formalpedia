-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_toInvariantRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:12.446844+00:00
-- url     : https://prove2.me/submissions/b2d30f5d-f7c4-420a-9c70-10dc41518291

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
omit [Algebra F K] [IsScalarTower F K B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : K) : (toInvariantRing G F K B k : B) = algebraMap K B k := rfl
end GroundTheory.PAdicHodge
