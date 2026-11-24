-- Prove2me | solution 1 for GlobalTheory.exists_isHilbertPoly_quotPiece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:37.518266+00:00
-- url     : https://prove2.me/submissions/9cdbd0bd-87aa-4b30-9c90-b25d61c7a112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_weightedHomogeneousComponent_one_mem
import Theorems.Thm_GlobalTheory_X_smul_mem_weightedHomogeneousSubmodule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∃ P : ℚ[X], IsHilbertPoly (quotPiece I) P ∧ P.degree < (Fintype.card ι : ℕ) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  have hfin := GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k)
  obtain ⟨P, hP, h⟩ := GradedHilbert.exists_polynomial_subquotient _
    (X_smul_mem_weightedHomogeneousSubmodule ι k) Finset.univ I ⊤ le_top
    (by
      intro n m hm
      have := weightedHomogeneousComponent_one_mem hI n hm
      rwa [← weightedDecomposition.decompose'_apply] at this) (by simp) (by simp)
  refine ⟨P, ⟨fun n => ?_, ?_⟩, hP⟩
  · haveI := hfin n
    unfold quotPiece
    infer_instance
  · filter_upwards [h] with n hn
    haveI := hfin n
    have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
      (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n)
    have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [e2, inf_comm] at e
    rw [Submodule.restrictScalars_top, top_inf_eq, ← e] at hn
    rw [← hn, quotPiece]
    push_cast
    ring
end GlobalTheory
