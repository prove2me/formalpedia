-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.qf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:34.995351+00:00
-- url     : https://prove2.me/submissions/abc04f5c-4727-467f-bfcd-b985808b1c17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (a x : n → K) (s : K) : qf a (s • x) = s ^ 2 * qf a x := by
  simp only [qf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.LocalQuad.FiveVar
