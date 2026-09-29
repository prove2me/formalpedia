-- Prove2me | solution 1 for ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/67fb34af-b139-50be-a8ad-8fe2e16bae39

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_apply_eq_single jq coeff_jq_pow_self coeff_jq_pow_of_lt PoleOrderLE"
p2m_open "ModularCurve"

theorem poleOrderLE_iff_le_order {f : LaurentSeries ℚ} (hf : f ≠ 0) {n : ℕ} :
    PoleOrderLE f n ↔ -(n : ℤ) ≤ f.order :=
  (HahnSeries.le_order_iff_forall hf).symm

theorem exists_poleOrderLE (f : LaurentSeries ℚ) : ∃ n : ℕ, PoleOrderLE f n :=
  ⟨(-f.order).toNat, fun _ hk => HahnSeries.coeff_eq_zero_of_lt_order (by omega)⟩

theorem poleOrderLE_aeval_jq (P : Polynomial ℚ) :
    PoleOrderLE (Polynomial.aeval jq P) P.natDegree := by
  intro k hk
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hile : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
    coeff_jq_pow_of_lt (by omega), mul_zero]

theorem coeff_aeval_jq_neg (P : Polynomial ℚ) {m : ℕ} (hm : P.natDegree ≤ m) :
    (Polynomial.aeval jq P).coeff (-(m : ℤ)) = P.coeff m := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single m]
  · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
      mul_one]
  · intro i hi hin
    have hilt : i < m :=
      lt_of_le_of_ne (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hm) hin
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro hm'
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simp only [Finset.mem_range, not_lt] at hm'; omega),
      zero_mul]

theorem poleOrderLE_sub_aeval_jq_succ {f : LaurentSeries ℚ} {n : ℕ}
    (hf : PoleOrderLE f (n + 1)) :
    PoleOrderLE
      (f - Polynomial.aeval jq
        (Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1))) n := by
  intro k hk
  rw [HahnSeries.coeff_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul]
  rcases (show k ≤ -((n + 1 : ℕ) : ℤ) by omega).eq_or_lt with heq | hlt
  · rw [heq, coeff_jq_pow_self, mul_one, sub_self]
  · rw [hf k hlt, coeff_jq_pow_of_lt hlt, mul_zero, sub_zero]

theorem exists_aeval_jq_sub_holomorphicAtInfty' (n : ℕ) :
    ∀ f : LaurentSeries ℚ, PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by
  induction n with
  | zero =>
    intro f hf
    exact ⟨0, by simp, by simpa using hf⟩
  | succ n ih =>
    intro f hf
    obtain ⟨Q, hQdeg, hQ⟩ := ih _ (poleOrderLE_sub_aeval_jq_succ hf)
    refine ⟨Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1) + Q, ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_)
      omega
    · intro k hk
      rw [map_add, sub_add_eq_sub_sub]
      exact hQ k hk

end ModularCurve

theorem solution (n : ℕ) :
    ∀ f : LaurentSeries ℚ, ModularCurve.PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ModularCurve.PoleOrderLE (f - Polynomial.aeval ModularCurve.jq P) 0 :=
  ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty' n

#print axioms solution

end
end S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty
end P2MW
export P2MW.S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty (solution)
