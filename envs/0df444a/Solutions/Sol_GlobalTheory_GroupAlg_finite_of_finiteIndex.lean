-- Prove2me | solution 1 for GlobalTheory.GroupAlg.finite_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:48.787805+00:00
-- url     : https://prove2.me/submissions/b27cb9bc-e420-4816-ba0f-a5c040e38f6a

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
theorem _root_.solution [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by
  letI := mapAlgebra R u
  exact Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)
end GlobalTheory.GroupAlg
