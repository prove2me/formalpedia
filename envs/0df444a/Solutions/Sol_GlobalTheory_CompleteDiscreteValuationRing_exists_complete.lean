-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.exists_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:54.062555+00:00
-- url     : https://prove2.me/submissions/7294317b-049b-4d73-bd1b-e9d4d94a079c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_dvr_of_principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : B →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧ IsLocalHom f := by
  let W := AdicCompletion (maximalIdeal B) B
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
  have h1 : maximalIdeal W = Ideal.span {algebraMap B W p} := by
    have h0 : Ideal.map (algebraMap B W) (maximalIdeal B) = Ideal.span {algebraMap B W p} := by
      generalize algebraMap B W = g
      exact (congrArg (Ideal.map g) hp.maximalIdeal_eq).trans
        (by rw [Ideal.map_span, Set.image_singleton])
    exact AdicCompletion.maximalIdeal_eq_map.trans h0
  have hr : ∀ x : B, x ≠ 0 → algebraMap B W x ∈ nonZeroDivisors W := by
    intro x hx
    have h2 : IsSMulRegular W x :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx)
    rw [mem_nonZeroDivisors_iff_left]
    intro y hy
    apply h2
    simp only [smul_zero]
    rw [Algebra.smul_def, hy]
  obtain ⟨hd, hD⟩ := dvr_of_principal W _ h1 (hr p hp.ne_zero)
  refine ⟨W, inferInstance, hd, hD, algebraMap B W, inferInstance, ?_, inferInstance⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h
  exact nonZeroDivisors.ne_zero (hr x h) hx
end GlobalTheory.CompleteDiscreteValuationRing
