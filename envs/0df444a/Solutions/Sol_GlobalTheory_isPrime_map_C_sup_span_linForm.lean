-- Prove2me | solution 1 for GlobalTheory.isPrime_map_C_sup_span_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:51.832222+00:00
-- url     : https://prove2.me/submissions/d91c1aa8-5a97-432c-938c-4817f2905522

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
theorem _root_.solution (S : Set ι) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (linForm u '' S)).IsPrime := by
  rw [← ker_map_comp_linFormElim u hu]
  exact RingHom.ker_isPrime _
end GlobalTheory
