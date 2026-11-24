-- Prove2me | solution 1 for GlobalTheory.linFormEquiv_symm_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:20.401048+00:00
-- url     : https://prove2.me/submissions/88ac0665-8483-4565-8f9d-611431148ef5

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
    (linFormEquiv u S j₀ hu).symm (linForm u i) = X (i, j₀) := by
  rw [AlgEquiv.symm_apply_eq, linFormEquiv_X_of_mem u hu hi]
end GlobalTheory
