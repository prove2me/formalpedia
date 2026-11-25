-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_isZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:29.708909+00:00
-- url     : https://prove2.me/submissions/c884b852-ce42-417a-9d4a-f63eb294702f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
attribute [instance 100] IsFiniteQC.isQuasicoherent
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution (h : IsZero F) : IsFiniteQC F :=
  .of_sum_eq_id (ι := Empty) (A := fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (h.eq_of_src _ _) (hA := fun i ↦ i.elim)
end IsFiniteQC
end GlobalTheory.QCoh
