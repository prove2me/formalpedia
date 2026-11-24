-- Prove2me | solution 1 for GlobalTheory.heightOneOrd_vw_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:08.900995+00:00
-- url     : https://prove2.me/submissions/12dfefaa-86d0-4e10-89ff-fc4503a76772

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
namespace GlobalTheory
theorem _root_.solution {ϖ : primeLocalSubalgebra K p} (hϖ : Irreducible ϖ) :
    heightOneOrd_vw p hp (ϖ : K) = 1 := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [heightOneOrd_vw, ← ordFrac_eq_heightOneOrdHom p hp (primeLocalSubalgebra K p)]
  exact (congrArg WithZero.log (Ring.ordFrac_irreducible (K := K) hϖ)).trans (WithZero.log_exp 1)
end GlobalTheory
