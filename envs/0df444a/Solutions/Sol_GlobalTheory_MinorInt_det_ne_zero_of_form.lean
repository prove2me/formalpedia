-- Prove2me | solution 1 for GlobalTheory.MinorInt.det_ne_zero_of_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:29.067129+00:00
-- url     : https://prove2.me/submissions/3673d653-1fff-4f45-af9e-c828a8af6e2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_form_diff_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨t, ht, hAt⟩ := exists_mulVec_eq_zero_iff.2 h0
  have h1 := h t
  rw [form_diff_re, hAt] at h1
  have h2 : 0 ≤ ∑ k, ‖(C *ᵥ t) k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : ∑ i, ‖t i‖ ^ 2 = 0 :=
    le_antisymm (by simp at h1; linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply ht
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h3 i (Finset.mem_univ _)
  simpa using this
end GlobalTheory.MinorInt
