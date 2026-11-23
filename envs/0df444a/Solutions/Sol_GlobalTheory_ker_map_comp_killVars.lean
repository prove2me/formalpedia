-- Prove2me | solution 1 for GlobalTheory.ker_map_comp_killVars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:49.523337+00:00
-- url     : https://prove2.me/submissions/8559fbfa-cf11-4e1a-9798-d4ebc0631857

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
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution (S : Set σ) (I : Ideal R) :
    RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp (killVars R S).toRingHom) =
      I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_killVars_map_C]
  rfl
end GlobalTheory
