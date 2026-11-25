-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.dpow_mul_dpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:00.818361+00:00
-- url     : https://prove2.me/submissions/01cb4567-c8cb-40da-8817-97870ec4a912

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe

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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (m n : ℕ) (x : AInf K p) :
    dpow m x * dpow n x = ((m + n).choose m : 𝔸) * dpow (m + n) x := by
  have hu := isUnit_natCast (K := K) (p := p) (Nat.factorial_ne_zero (m + n))
  apply hu.mul_left_cancel
  have h : ((m + n).factorial : 𝔸) = ((m + n).choose m : 𝔸) * m.factorial * n.factorial := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial m n, Nat.cast_mul, Nat.cast_mul,
      Nat.choose_symm_add]
  calc ((m + n).factorial : 𝔸) * (dpow m x * dpow n x)
      = ((m + n).choose m : 𝔸) * ((m.factorial * dpow m x) * (n.factorial * dpow n x)) := by
        rw [h]; ring
    _ = ((m + n).choose m : 𝔸) * algebraMap (AInf K p) 𝔸 x ^ (m + n) := by
        rw [factorial_mul_dpow, factorial_mul_dpow, pow_add]
    _ = ((m + n).factorial : 𝔸) * (((m + n).choose m : 𝔸) * dpow (m + n) x) := by
        rw [← factorial_mul_dpow (m + n) x]; ring
end GroundTheory.PAdicHodge.ACris
