-- Prove2me | solution 1 for GroundTheory.LocalField.exists_zpow_mul_zpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:21.6408+00:00
-- url     : https://prove2.me/submissions/a4ad18cb-3311-47f0-bb20-81c2c8062be1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}
namespace GroundTheory.LocalField
theorem _root_.solution (hp : p.Prime) (s : G) :
    ∃ a b : ℤ, s ^ a * s ^ b = s ∧ (orderOf (s ^ a)).Coprime p ∧
      (s ^ b) ^ (p ^ (orderOf s).factorization p) = 1 := by
  set o := orderOf s
  have ho : o ≠ 0 := (orderOf_pos s).ne'
  set k := o.factorization p
  set r := o / p ^ k
  have hor : p ^ k * r = o := Nat.ordProj_mul_ordCompl_eq_self o p
  have hr : r.Coprime p := (Nat.coprime_ordCompl hp ho).symm
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (r : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k hr.symm)
  obtain ⟨u, v, huv⟩ := hcop
  have hso : s ^ (o : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨u * (p ^ k : ℕ), v * r, ?_, ?_, ?_⟩
  · rw [← zpow_add, huv, zpow_one]
  · have h1 : (s ^ (u * (p ^ k : ℕ) : ℤ)) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show u * ((p ^ k : ℕ) : ℤ) * (r : ℤ) = u * (o : ℤ) by
        rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hr
  · rw [← zpow_natCast, ← zpow_mul, show v * (r : ℤ) * ((p ^ k : ℕ) : ℤ) = v * (o : ℤ) by
      rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]
end GroundTheory.LocalField
