-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.span_coeff_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:00.419554+00:00
-- url     : https://prove2.me/submissions/9414c760-ac62-423e-a60f-bbfce2d86564

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.GaussContentLinearForms
variable {V : Type} [CommRing V] {σ : Type}
namespace GlobalTheory.GaussContentLinearForms
theorem _root_.solution [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by
  have h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔
      Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V := by
    rw [Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]
    refine forall_congr' fun s => ?_
    rw [coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff]
    rfl
  rw [ne_eq, h1]
  constructor
  · intro h h'
    rw [h, top_le_iff] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top h'
  · intro h
    by_contra h'
    exact h (IsLocalRing.le_maximalIdeal h')
end GlobalTheory.GaussContentLinearForms
