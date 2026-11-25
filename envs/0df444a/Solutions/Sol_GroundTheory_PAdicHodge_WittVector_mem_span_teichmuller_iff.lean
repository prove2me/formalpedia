-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.mem_span_teichmuller_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:05.949462+00:00
-- url     : https://prove2.me/submissions/f301e0bd-f988-4edc-9e68-2602a86af110

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmuller_mul_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (b : R) (y : WittVector p R) :
    y ∈ Ideal.span {teichmuller p b} ↔ ∀ n, b ^ p ^ n ∣ y.coeff n := by
  constructor
  · intro h n
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [mul_comm, WittVector.teichmuller_mul_coeff]
    exact dvd_mul_right _ _
  · intro h
    choose w hw using h
    refine Ideal.mem_span_singleton'.2 ⟨WittVector.mk p w, ?_⟩
    ext n
    rw [mul_comm, WittVector.teichmuller_mul_coeff, coeff_mk, hw]
end WittVector
end GroundTheory.PAdicHodge
