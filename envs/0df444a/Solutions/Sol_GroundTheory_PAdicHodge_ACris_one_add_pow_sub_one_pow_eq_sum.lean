-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.one_add_pow_sub_one_pow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:58.155293+00:00
-- url     : https://prove2.me/submissions/368c7281-83ac-4555-b905-b4270aa9cf95

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_natDegree_one_add_X_pow_sub_one_pow_le

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
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (x : AInf K p) (N L : ℕ) (hL : p * N ≤ L) :
    ((1 + x) ^ p - 1) ^ N =
      ∑ m ∈ Finset.range (L + 1), (powCoeff p N m : AInf K p) * x ^ m := by
  have hdeg : ((((1 : ℤ[X]) + X) ^ p - 1) ^ N).natDegree < L + 1 :=
    Nat.lt_succ_of_le ((natDegree_one_add_X_pow_sub_one_pow_le p N).trans hL)
  have h := aeval_eq_sum_range' (R := ℤ) hdeg x
  simp only [map_pow, map_sub, map_add, map_one, aeval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [zsmul_eq_mul, powCoeff]
end GroundTheory.PAdicHodge.ACris
