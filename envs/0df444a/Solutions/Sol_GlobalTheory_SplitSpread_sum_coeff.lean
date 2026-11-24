-- Prove2me | solution 1 for GlobalTheory.SplitSpread.sum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:03.34184+00:00
-- url     : https://prove2.me/submissions/88147f75-bf36-4c4e-ae2d-ca4f60ccc2db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Theorems.Thm_GlobalTheory_SplitSpread_sum_eq_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
variable {A D}
namespace GlobalTheory.SplitSpread
theorem _root_.solution {k : Type} [CommRing k] (p : MvPolynomial σ k) (hp : p.totalDegree ≤ D) :
    ∑ m : Mon σ D, monomial m.1 (coeff m.1 p) = p := by
  classical
  ext n
  simp only [coeff_sum, coeff_monomial]
  by_cases hn : n.degree ≤ D
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro m _ hm
      rw [if_neg]
      intro h; exact hm (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hn ((sum_eq_degree n ▸ le_totalDegree (mem_support_iff.mpr (Ne.symm h))).trans hp)
    · intro m _
      rw [if_neg]
      rintro rfl; exact hn m.2
end GlobalTheory.SplitSpread
