-- Prove2me | solution 1 for GlobalTheory.linFormEquiv_symm_X_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:19.182732+00:00
-- url     : https://prove2.me/submissions/646a206d-fe5b-4655-beba-aa7aac77b3b1

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
namespace GlobalTheory
theorem _root_.solution {S : Set ι} {i : ι} (hi : i ∈ S) :
    (linFormEquiv u S j₀ hu).symm (X (i, j₀)) = linForm (linFormInvCoeff u j₀ hu) i :=
  linFormHom_X_of_mem _ j₀ hi
end GlobalTheory
