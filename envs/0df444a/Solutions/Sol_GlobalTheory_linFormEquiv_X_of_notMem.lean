-- Prove2me | solution 1 for GlobalTheory.linFormEquiv_X_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:17.48208+00:00
-- url     : https://prove2.me/submissions/aaffc29e-3cf6-47b6-bbcb-a7d2fd08f51f

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
theorem _root_.solution {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    linFormEquiv u S j₀ hu (X x) = X x :=
  linFormHom_X_of_notMem u hx
end GlobalTheory
