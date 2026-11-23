-- Prove2me | solution 1 for GlobalTheory.isPrime_span_linForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:37.69223+00:00
-- url     : https://prove2.me/submissions/ffc6b7d8-65b8-46fa-8c82-eec30fbb736b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
namespace GlobalTheory
theorem _root_.solution [IsDomain R] (S : Set ι) :
    (Ideal.span (linForm u '' S)).IsPrime := by
  rw [← ker_linFormElim u hu]
  exact RingHom.ker_isPrime _
end GlobalTheory
