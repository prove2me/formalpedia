-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.aTerm_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:33.512521+00:00
-- url     : https://prove2.me/submissions/c698e5b1-bfcd-49b9-a83c-c5730c53efe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (k : ℕ) :
    aTerm q N X α (k : ℤ) = ((q : ℂ) ^ (N + 1) * X * α) ^ k := by
  have h : (q : ℂ) ^ (-(k : ℤ) * ((N : ℤ) + 1)) = ((q : ℂ) ^ ((N + 1) * k))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring
  have h2 : (q : ℂ) ^ ((2 * N + 2) * k) = (q : ℂ) ^ ((N + 1) * k) * (q : ℂ) ^ ((N + 1) * k) := by
    rw [← pow_add]
    congr 1
    ring
  have h3 : (q : ℂ) ^ ((N + 1) * k) ≠ 0 := pow_ne_zero _ hq
  rw [aTerm, h, Int.toNat_natCast, Int.natAbs_natCast, zpow_natCast, h2, mul_pow, mul_pow, ← pow_mul]
  field_simp
end GlobalTheory.CompanionTheory.InertLevi
