-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.bf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:44.939705+00:00
-- url     : https://prove2.me/submissions/f5e004c5-e1ff-4a2b-aee0-2e760a5a3a54

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
theorem _root_.solution (a x y : n → K) (s : K) : bf a (s • x) y = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.LocalQuad.FiveVar
