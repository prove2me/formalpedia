-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:08.798807+00:00
-- url     : https://prove2.me/submissions/04ae9597-5679-43fc-9b0f-5805bd739d3c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (a : V) : wedgeT (R := R) V (a ⊗ₜ[R] a) = 0 := by
  rw [wedgeT_tmul]
  exact (exteriorPower.ιMulti R (M := V) 2).map_eq_zero_of_eq ![a, a]
    (i := 0) (j := 1) rfl (by decide)
end GlobalTheory.CompanionTheory.WedgeOf
