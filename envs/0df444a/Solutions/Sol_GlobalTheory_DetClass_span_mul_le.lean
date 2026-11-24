-- Prove2me | solution 1 for GlobalTheory.DetClass.span_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:01.116188+00:00
-- url     : https://prove2.me/submissions/6f7a9ff6-ca0a-4e6b-b6fa-ff75a526045c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
import Theorems.Thm_GlobalTheory_DetClass_det_mem
import Theorems.Thm_GlobalTheory_DetClass_det_swap

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
open Pointwise
namespace GlobalTheory.DetClass
theorem _root_.solution {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (b : (i : ι) → I i) :
    Ideal.span {(mat φ b).det} * ∏ i, I i ≤ Ideal.span {∏ i, (b i : R)} * ∏ j, J j := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hP : ∏ i, I i = Submodule.span R (∏ i, (I i : Set R)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hP] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).mp hx
    have hs := det_swap φ (fun i => ⟨g i, hg (Finset.mem_univ i)⟩) b
    simp only at hs
    rw [mul_comm ((mat φ b).det), ← hs]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (det_mem φ _)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Ideal.add_mem _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r hx
end GlobalTheory.DetClass
