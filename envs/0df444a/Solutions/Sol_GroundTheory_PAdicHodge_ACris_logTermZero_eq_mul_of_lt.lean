-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.logTermZero_eq_mul_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:03.905927+00:00
-- url     : https://prove2.me/submissions/a9ffbffd-2709-46de-8ad1-a99d7c458f5a

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
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ} (hn : n + 1 < p) :
    ∃ w : ACrisZero K p, logTermZero hx n = algebraMap (AInf K p) (ACrisZero K p) x * w := by
  have hcop : (n + 1).Coprime p := (Nat.coprime_of_lt_prime (Nat.succ_ne_zero n) hn hp.out).symm
  have hu := WittVector.isUnit_natCast_of_coprime (R := 𝒪♭) hcop
  refine ⟨(-1) ^ n * algebraMap (AInf K p) (ACrisZero K p) (x ^ n * ↑hu.unit⁻¹), ?_⟩
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, Subalgebra.coe_algebraMap, coe_dpowZero]
  have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
  apply h1.mul_left_cancel
  have h2 : ((n + 1 : ℕ) : 𝔸) * (n.factorial : 𝔸) = ((n + 1).factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.factorial_succ]
  have h3 : ((n + 1 : ℕ) : 𝔸) * algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ = 1 := by
    rw [← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, IsUnit.mul_val_inv, map_one]
  calc ((n + 1 : ℕ) : 𝔸) * ((-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x)
      = (-1) ^ n * (((n + 1 : ℕ) : 𝔸) * n.factorial * dpow (n + 1) x) := by ring
    _ = (-1) ^ n * algebraMap (AInf K p) 𝔸 x ^ (n + 1) := by
        rw [h2, factorial_mul_dpow]
    _ = ((n + 1 : ℕ) : 𝔸) * (algebraMap (AInf K p) 𝔸 x *
        ((-1) ^ n * algebraMap (AInf K p) 𝔸 (x ^ n * ↑hu.unit⁻¹))) := by
        rw [map_mul, map_pow]
        linear_combination (-1) ^ n * algebraMap (AInf K p) 𝔸 x ^ (n + 1) * h3.symm
end GroundTheory.PAdicHodge.ACris
