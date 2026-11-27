-- Prove2me | solution 1 for GlobalTheory.length_quotient_span_ne_top_of_discr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:32.172807+00:00
-- url     : https://prove2.me/submissions/f01b8356-fb88-420b-b4ad-b79c08b793e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_discr_eq_basis_det_sq_mul
import Theorems.Thm_GlobalTheory_length_quotient_span_ne_top_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
variable [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {v : ι → S}
    (hv : Algebra.discr R v ≠ 0) :
    Module.length R (S ⧸ Submodule.span R (Set.range v)) ≠ ⊤ := by
  rw [length_quotient_span_ne_top_iff e]
  intro h
  rw [discr_eq_basis_det_sq_mul e, h] at hv
  simp at hv
end GlobalTheory
