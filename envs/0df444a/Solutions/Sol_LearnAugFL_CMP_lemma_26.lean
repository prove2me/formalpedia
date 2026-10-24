-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_26
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:44:53.153329+00:00
-- url     : https://prove2.me/submissions/8ae1ec19-02ed-4cad-8694-4dbf24f94ec3

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP.RayProof

lemma sum_update {n : ℕ} (P : Fin n → Pt) (i : Fin n) (q z : Pt) :
    ∑ j, dist z (Function.update P i q j) =
      (∑ j ∈ Finset.univ.erase i, dist z (P j)) + dist z q := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma dist_ray (o p : Pt) (t : ℝ) (ht : 0 ≤ t) :
    dist o (o + t • (p - o)) = t * dist o p := by
  rw [dist_eq_norm, show o - (o + t • (p - o)) = t • (o - p) by module,
    norm_smul_of_nonneg ht, dist_eq_norm]

end LearnAugFL.CMP.RayProof

open LearnAugFL.CMP

theorem solution {n : ℕ} (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (i : Fin n)
    (hi : P i ≠ o) (t : ℝ) (ht : 0 ≤ t) :
    IsOpt (Function.update P i (o + t • (P i - o))) o := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hsum (z : Pt) : (∑ j, dist o (P j)) ≤ ∑ j, dist z (P j) := by
    exact (div_le_div_iff_of_pos_right hn).mp (hP z)
  let R : Pt → ℝ := fun z => ∑ j ∈ Finset.univ.erase i, dist z (P j)
  have hsplit (z : Pt) : (∑ j, dist z (P j)) = R z + dist z (P i) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have hopt (z : Pt) : R o + dist o (P i) ≤ R z + dist z (P i) := by
    simpa only [hsplit] using hsum z
  let q := o + t • (P i - o)
  have hq : dist o q = t * dist o (P i) := RayProof.dist_ray o (P i) t ht
  intro z
  apply (div_le_div_iff_of_pos_right hn).mpr
  rw [RayProof.sum_update, RayProof.sum_update]
  change R o + dist o q ≤ R z + dist z q
  by_cases ht1 : t ≤ 1
  · have hpq : dist q (P i) = (1 - t) * dist o (P i) := by
      rw [dist_comm, dist_eq_norm,
        show P i - q = (1 - t) • (P i - o) by dsimp [q]; module,
        norm_smul_of_nonneg (sub_nonneg.mpr ht1), ← dist_eq_norm, dist_comm (P i) o]
    have htri := dist_triangle z q (P i)
    rw [hpq] at htri
    have horig := hopt z
    rw [hq]
    nlinarith
  · have htpos : 0 < t := lt_trans zero_lt_one (lt_of_not_ge ht1)
    have htinv : 0 < t⁻¹ := inv_pos.mpr htpos
    have htinv1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge ht1))
    let w := o + t⁻¹ • (z - o)
    have hw : w = (1 - t⁻¹) • o + t⁻¹ • z := by dsimp [w]; module
    have hwp : dist w (P i) = t⁻¹ * dist z q := by
      have heq : w - P i = t⁻¹ • (z - q) := by
        dsimp [w, q]
        simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
        abel
      rw [dist_eq_norm, heq, norm_smul_of_nonneg htinv.le, dist_eq_norm]
    have hR : R w ≤ (1 - t⁻¹) * R o + t⁻¹ * R z := by
      dsimp [R]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      have hc := (convexOn_univ_dist (P j)).2 (Set.mem_univ o) (Set.mem_univ z)
        (sub_nonneg.mpr htinv1) htinv.le (sub_add_cancel 1 t⁻¹)
      simpa only [hw, smul_eq_mul] using hc
    have horig := hopt w
    rw [hwp] at horig
    have hscaled : t⁻¹ * (R o + t * dist o (P i)) ≤ t⁻¹ * (R z + dist z q) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul, mul_add]
      nlinarith only [hR, horig]
    rw [hq]
    exact (mul_le_mul_iff_right₀ htinv).mp hscaled
