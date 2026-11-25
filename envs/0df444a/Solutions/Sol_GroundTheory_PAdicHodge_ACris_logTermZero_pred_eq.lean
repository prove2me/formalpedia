-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.logTermZero_pred_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:46.688687+00:00
-- url     : https://prove2.me/submissions/6a23bd84-8465-4937-9cfb-50113a44d56d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
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
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) {c : ACrisZero K p}
    (hc : (algebraMap (AInf K p) (ACrisZero K p) x) ^ (p - 1) = (p : ACrisZero K p) * c) :
    logTermZero hx (p - 1) = algebraMap (AInf K p) (ACrisZero K p) x * ((-1) ^ (p - 1) * c) := by
  have hcc := congrArg (fun y : ACrisZero K p => (y : 𝔸)) hc
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, Subalgebra.coe_algebraMap, coe_dpowZero] at hcc ⊢
  have h1 := isUnit_natCast (K := K) (p := p) hp.out.ne_zero
  apply h1.mul_left_cancel
  rw [Nat.sub_add_cancel hp.out.one_le]
  have h2 : (p : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  calc (p : 𝔸) * ((-1) ^ (p - 1) * ((p - 1).factorial : 𝔸) * dpow p x)
      = (-1) ^ (p - 1) * ((p : 𝔸) * (p - 1).factorial * dpow p x) := by ring
    _ = (-1) ^ (p - 1) * (algebraMap (AInf K p) 𝔸 x * algebraMap (AInf K p) 𝔸 x ^ (p - 1)) := by
        rw [h2, factorial_mul_dpow, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    _ = (p : 𝔸) * (algebraMap (AInf K p) 𝔸 x * ((-1) ^ (p - 1) * (c : 𝔸))) := by
        rw [hcc]; ring
end GroundTheory.PAdicHodge.ACris
