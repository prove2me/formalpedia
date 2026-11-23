-- Prove2me | solution 1 for GlobalTheory.X_smul_mem_weightedHomogeneousSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.836228+00:00
-- url     : https://prove2.me/submissions/0b856c92-ccb4-4ef7-834e-208769ad0d78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module MvPolynomial
variable (ι k : Type*) [Field k]
namespace GlobalTheory
theorem _root_.solution (i : ι) (n : ℤ) (m : MvPolynomial ι k)
    (hm : m ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n) :
    (MvPolynomial.X i : MvPolynomial ι k) • m ∈
      weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) (n + 1) := by
  rw [mem_weightedHomogeneousSubmodule] at hm ⊢
  rw [smul_eq_mul, add_comm]
  exact (isWeightedHomogeneous_X k (fun _ : ι => (1 : ℤ)) i).mul hm
end GlobalTheory
