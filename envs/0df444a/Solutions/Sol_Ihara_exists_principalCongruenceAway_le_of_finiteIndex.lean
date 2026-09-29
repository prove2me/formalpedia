-- Prove2me | solution 1 for Ihara.exists_principalCongruenceAway_le_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/984b3b37-8cb3-5bc7-9c12-dfb22d1b69d2

import Definitions.Def_IharaMennickeCarrier
import Theorems.Thm_Ihara_mennickeCSP_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_exists_principalCongruenceAway_le_of_finiteIndex

set_option autoImplicit false

open Ihara

open scoped MatrixGroups

namespace MennickeConjugation

private theorem inv_mul_mul_pow {G : Type*} [Group G] (u x : G) (m : ℕ) :
    (u⁻¹ * x * u) ^ m = u⁻¹ * x ^ m * u := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, mul_inv_cancel_left]

private theorem inv_mul_mul_eq_one_iff {G : Type*} [Group G] (u y : G) :
    u⁻¹ * y * u = 1 ↔ y = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun z => u * z * u⁻¹) h
    simpa [mul_assoc] using h'
  · intro h
    simp [h]

private theorem orderOf_pow_eq_of_conj {G : Type*} [Group G] (u x : G) (k : ℕ)
    (h : u⁻¹ * x * u = x ^ k) : orderOf (x ^ k) = orderOf x := by
  rw [← h, orderOf_eq_orderOf_iff]
  intro n
  rw [inv_mul_mul_pow, inv_mul_mul_eq_one_iff]

private theorem coprime_orderOf_of_conj {G : Type*} [Group G] [Finite G] (u x : G) {q : ℕ}
    (hq : q ≠ 0) (h : u⁻¹ * x * u = x ^ (q ^ 2)) : Nat.Coprime (orderOf x) q := by
  have hk := orderOf_pow_eq_of_conj u x (q ^ 2) h
  rw [orderOf_pow' x (pow_ne_zero 2 hq), Nat.div_eq_self] at hk
  exact (Nat.coprime_pow_right_iff two_pos _ _).mp
    (Nat.coprime_iff_gcd_eq_one.mpr (hk.resolve_left (orderOf_pos x).ne'))

private theorem conj_mennickeA (q : ℕ) :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  apply Subtype.ext
  have hA : ((slToAway q mennickeA : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; 1, 1] := by
    rw [coe_slToAway, mennickeA_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hAk : (((slToAway q mennickeA) ^ (q ^ 2) : SL(2, ZAway q)) :
      Matrix (Fin 2) (Fin 2) (ZAway q)) = !![1, 0; ((q : ℕ) : ZAway q) ^ 2, 1] := by
    rw [← map_pow, coe_slToAway, mennickeA_pow_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, mennickeU_coe, Matrix.adjugate_fin_two_of, hA, hAk,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q, natCast_q_mul_qInv, pow_two]

private theorem exists_pow_mem_of_finiteIndex {q : ℕ} (hq : q.Prime)
    (H : Subgroup SL(2, ZAway q)) [H.Normal] [H.FiniteIndex] :
    ∃ d : ℕ, 0 < d ∧ Nat.Coprime d q ∧ (slToAway q mennickeA) ^ d ∈ H := by
  refine ⟨orderOf (QuotientGroup.mk' H (slToAway q mennickeA)), orderOf_pos _, ?_, ?_⟩
  · refine coprime_orderOf_of_conj (QuotientGroup.mk' H (mennickeU q)) _ hq.ne_zero ?_
    rw [← map_inv, ← map_mul, ← map_mul, conj_mennickeA q, map_pow]
  · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact pow_orderOf_eq_one _

private theorem normalClosure_pow_le {q : ℕ} (H : Subgroup SL(2, ZAway q)) [H.Normal] {d : ℕ}
    (hd : (slToAway q mennickeA) ^ d ∈ H) :
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ d} : Set SL(2, ZAway q)) ≤ H :=
  Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hd)

end MennickeConjugation

open MennickeConjugation in
theorem solution {q : ℕ} (hq : q.Prime)
    (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex] :
    ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K := by
  obtain ⟨d, hd0, hdq, hdmem⟩ := exists_pow_mem_of_finiteIndex hq K.normalCore
  refine ⟨d, hdq, hd0.ne', ?_⟩
  calc Ihara.principalCongruenceAway d q hdq
      ≤ Subgroup.normalClosure ({(slToAway q mennickeA) ^ d} : Set SL(2, ZAway q)) :=
        (mennickeCSP_iff_ker_le d q hdq).mp (Ihara.mennickeCSP_of_prime q hq d hdq)
    _ ≤ K.normalCore := normalClosure_pow_le K.normalCore hdmem
    _ ≤ K := Subgroup.normalCore_le K

end S_Ihara_exists_principalCongruenceAway_le_of_finiteIndex
end P2MW
export P2MW.S_Ihara_exists_principalCongruenceAway_le_of_finiteIndex (solution)
