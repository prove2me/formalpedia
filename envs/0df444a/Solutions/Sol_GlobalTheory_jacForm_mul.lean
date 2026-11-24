-- Prove2me | solution 1 for GlobalTheory.jacForm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:24.275932+00:00
-- url     : https://prove2.me/submissions/441e614a-cc9b-4ee3-9a2e-45cbc998e95a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jetWedge_shear
import Theorems.Thm_GlobalTheory_jacForm_eq_jetWedge

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
theorem _root_.solution (h : A) (f : Fin (D + 1) → A) :
    jacForm d ω (fun i => h * f i) = h ^ (D + 1) • jacForm d ω f := by
  rw [jacForm_eq_jetWedge, jacForm_eq_jetWedge, ← jetWedge_shear ω h (d h)]
  simp only [Derivation.leibniz]
end GlobalTheory
