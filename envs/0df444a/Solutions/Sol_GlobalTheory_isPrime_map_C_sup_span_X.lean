-- Prove2me | solution 1 for GlobalTheory.isPrime_map_C_sup_span_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:48.564898+00:00
-- url     : https://prove2.me/submissions/38922482-c1f9-48c2-8b33-92a87b1fa400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_ker_map_comp_killVars

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
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution (S : Set σ) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)).IsPrime := by
  rw [← ker_map_comp_killVars]
  exact RingHom.ker_isPrime _
end GlobalTheory
