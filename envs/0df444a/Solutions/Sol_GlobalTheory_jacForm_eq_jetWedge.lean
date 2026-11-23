-- Prove2me | solution 1 for GlobalTheory.jacForm_eq_jetWedge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:35.983613+00:00
-- url     : https://prove2.me/submissions/eda254b5-6ace-41ef-ad70-825e890823c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jetWedge_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
namespace GlobalTheory
theorem _root_.solution (f : Fin (D + 1) → A) :
    jacForm d ω f = jetWedge ω (fun i => (f i, d (f i))) := by
  rw [jetWedge_apply, jacForm]
end GlobalTheory
