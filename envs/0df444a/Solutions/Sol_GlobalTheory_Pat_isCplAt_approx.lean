-- Prove2me | solution 1 for GlobalTheory.Pat.isCplAt_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:12.963803+00:00
-- url     : https://prove2.me/submissions/d3b8707b-5b32-4fb4-91bc-f0cc60768a17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Theorems.Thm_GlobalTheory_Pat_IsCplAt_approx_surj
import Theorems.Thm_GlobalTheory_Pat_IsCplAt_approx_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
    [q.IsPrime] (φ : R →+* S), IsCplAt q φ → ∀ k : ℕ,
    (∀ s : S, ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k) ∧
      ∀ a : R, φ a ∈ maximalIdeal S ^ k → ∃ b ∉ q, b * a ∈ q ^ k :=
  fun _ _ _ _ _ _ _ _ h k => ⟨h.approx_surj k, h.approx_inj k⟩
end GlobalTheory.Pat
