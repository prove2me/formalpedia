-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.sum_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:35.077794+00:00
-- url     : https://prove2.me/submissions/2601eaa3-ae46-4086-830e-35f560e7dbe5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_pts_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution (B : Submodule R M) (f : M → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) :
    ∑ y ∈ pts B, f y = if ∀ y ∈ B, f y = 1 then ((pts B).card : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl fun y hy => h y (mem_pts.mp hy)]
    simp
  · push Not at h
    obtain ⟨y0, hy0, hne⟩ := h
    have h1 : ∑ y ∈ pts B, f (y + y0) = ∑ y ∈ pts B, f y := sum_pts_add B f hy0
    simp_rw [hf] at h1
    rw [← Finset.sum_mul] at h1
    have h2 : (∑ y ∈ pts B, f y) * (f y0 - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne
end GlobalTheory.HermitianGauss
