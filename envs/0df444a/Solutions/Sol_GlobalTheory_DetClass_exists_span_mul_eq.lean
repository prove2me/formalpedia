-- Prove2me | solution 1 for GlobalTheory.DetClass.exists_span_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:29.764836+00:00
-- url     : https://prove2.me/submissions/aadd4d44-94b8-4c54-b60f-12a3932c416c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
import Theorems.Thm_GlobalTheory_DetClass_span_mul_le
import Theorems.Thm_GlobalTheory_DetClass_mat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DetClass
theorem _root_.solution [IsDomain R] {I J : ι → Ideal R}
    (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hc0 : c ≠ 0) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * ∏ i, I i = Ideal.span {y} * ∏ i, J i := by
  set d : R := ∏ _i : ι, c with hd
  have h1 := span_mul_le φ.toLinearMap (fun i => ⟨c, hI i⟩)
  have h2 := span_mul_le φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)
  simp only at h1 h2
  rw [← hd] at h1 h2
  set x := (mat φ.toLinearMap (fun i => ⟨c, hI i⟩)).det
  set y := (mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)).det
  have hyx : y * x = d * d := by
    have h := congrArg Matrix.det (mat_mul φ c hI hJ)
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_mul_distrib] at h
    exact h
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => hc0
  have hdd : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hy0 : y ≠ 0 := fun h => hdd (by rw [← hyx, h, zero_mul])
  refine ⟨d * d, d * y, hdd, mul_ne_zero hd0 hy0, le_antisymm ?_ ?_⟩
  · rw [← hyx, ← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_comm (Ideal.span {d}), mul_assoc]
    exact Ideal.mul_mono_right h1
  · rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    exact Ideal.mul_mono_right h2
end GlobalTheory.DetClass
