-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.fockQ_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:05.738774+00:00
-- url     : https://prove2.me/submissions/feaf4824-e06b-460e-a11b-58149d90c9ce

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_component_eq_smul_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution : Formalism.GradedWeylDivisibility.FockQHW := by
  classical
  intro r n hn ν hν F hF
  have h := component_eq_smul_hw hn hν hF
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' := hwRowWeight ℚ r n hn ν hν (mem_support_iff.mp hm)
  have h2 := congrArg (coeff m) h
  rw [coeff_weightedHomogeneousComponent, if_pos hw', coeff_smul, smul_eq_mul] at h2
  rw [h2]
  ring
end GlobalTheory.FockHighestWeight
