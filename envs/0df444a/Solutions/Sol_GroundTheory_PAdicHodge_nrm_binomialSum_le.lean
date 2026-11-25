-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_binomialSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:20.006349+00:00
-- url     : https://prove2.me/submissions/69a86d0e-5bb9-4560-9709-f08c0e45d91d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sum_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_natCast_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_one_of_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {p : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x y : Ω) (hx : nrm K x ≤ 1) (hy : nrm K y ≤ 1) :
    nrm K (∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω)) ≤ 1 := by
  refine nrm_sum_le zero_le_one fun k _ ↦ ?_
  exact nrm_mul_le_one (nrm_mul_le_one (nrm_le_one_of_pow hx _) (nrm_le_one_of_pow hy _))
    (nrm_natCast_le_one _)
end GroundTheory.PAdicHodge
