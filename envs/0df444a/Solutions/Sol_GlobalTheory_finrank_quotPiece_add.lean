-- Prove2me | solution 1 for GlobalTheory.finrank_quotPiece_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:00.598134+00:00
-- url     : https://prove2.me/submissions/0f2f3110-902f-4e51-a6fd-920f64673931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_quotPiece_natCast

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
theorem _root_.solution [Finite ι] (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    finrank k (quotPiece I n) +
      finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) =
      finrank k (homogeneousSubmodule ι k n) := by
  have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
    (homogeneousSubmodule ι k n)
  have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
    ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [e2, inf_comm] at e
  rw [quotPiece_natCast, e]
end GlobalTheory
