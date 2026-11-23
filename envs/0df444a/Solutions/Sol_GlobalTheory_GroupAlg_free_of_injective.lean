-- Prove2me | solution 1 for GlobalTheory.GroupAlg.free_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:37.038796+00:00
-- url     : https://prove2.me/submissions/c4e23bb3-c05c-427b-8e2e-cda0b3e339be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Free R[Y] R[X] :=
  letI := mapAlgebra R u
  .of_basis (cosetBasis R u hu)
end GlobalTheory.GroupAlg
