-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.logTermZero_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:31.0468+00:00
-- url     : https://prove2.me/submissions/967741db-de0f-4407-87c9-c6359a978957

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_factorial_mul_dpow_eq_sum
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_dpowZero


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
variable {x : AInf K p}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (hx : x ∈ RingHom.ker θ) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermZero (one_add_pow_sub_one_mem hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero, AddSubmonoidClass.coe_finsetSum,
    SubringClass.coe_intCast]
  rw [mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logCoeff]
  push_cast
  ring
end GroundTheory.PAdicHodge.ACris
