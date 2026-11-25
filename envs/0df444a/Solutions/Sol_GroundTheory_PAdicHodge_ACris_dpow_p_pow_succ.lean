-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.dpow_p_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:57.170387+00:00
-- url     : https://prove2.me/submissions/0f9e2c5e-23cc-4464-8af7-5f1189fde47b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_mul_dpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (x : AInf K p) (j : ℕ) :
    dpow p x ^ (j + 1) =
      ((∏ i ∈ Finset.range j, ((i + 2) * p).choose p : ℕ) : 𝔸) * dpow ((j + 1) * p) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : (j + 1) * p + p = (j + 2) * p := by ring
    have e2 : (j + 1 + 1) * p = (j + 2) * p := by ring
    rw [pow_succ, ih, mul_assoc, dpow_mul_dpow, Nat.choose_symm_add, e, e2,
      Finset.prod_range_succ, Nat.cast_mul]
    ring
end GroundTheory.PAdicHodge.ACris
