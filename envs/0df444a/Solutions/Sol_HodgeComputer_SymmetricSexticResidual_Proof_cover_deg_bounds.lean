-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_deg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:26:48.232467+00:00
-- url     : https://prove2.me/submissions/8a2d394f-efa4-4a83-a475-242d5e434bd8

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_CoverParams
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators LaurentSeries PowerSeries

noncomputable section CoverDegBounds

private lemma deg2_q20 : k5Params.q20.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_q11 : k5Params.q11.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_q02 : k5Params.q02.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_c30 : k5Params.c30.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_c21 : k5Params.c21.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_c12 : k5Params.c12.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_c03 : k5Params.c03.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_ca : k5Params.ca_h.natDegree ≤ 2 := quadU_natDegree_le _ _ _
private lemma deg2_cb : k5Params.cb_h.natDegree ≤ 2 := quadU_natDegree_le _ _ _

private lemma coeff_mul_top2 (a b : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) :
    (a * b).coeff 4 = a.coeff 2 * b.coeff 2 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * b.coeff j),
    Finset.sum_eq_single 2]
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < 4 - i), mul_zero]
  · intro h; simp at h

private lemma coeff_mul_top3 (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).coeff 6 = a.coeff 2 * b.coeff 2 * c.coeff 2 := by
  have hbc : (b * c).natDegree ≤ 4 := (Polynomial.natDegree_mul_le).trans (by omega)
  rw [mul_assoc, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * (b * c).coeff j),
    Finset.sum_eq_single 2]
  · rw [show 6 - 2 = 4 by rfl, coeff_mul_top2 b c hb hc]; ring
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (b * c).natDegree < 6 - i), mul_zero]
  · intro h; simp at h

private lemma coeff_mul_top4 (a b c d : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2) :
    (a * b * c * d).coeff 8 = a.coeff 2 * b.coeff 2 * c.coeff 2 * d.coeff 2 := by
  have hab : (a * b).natDegree ≤ 4 := (Polynomial.natDegree_mul_le).trans (by omega)
  have hcd : (c * d).natDegree ≤ 4 := (Polynomial.natDegree_mul_le).trans (by omega)
  have heq : a * b * c * d = (a * b) * (c * d) := by ring
  rw [heq, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a * b).coeff i * (c * d).coeff j),
    Finset.sum_eq_single 4]
  · rw [show 8 - 4 = 4 by rfl, coeff_mul_top2 a b ha hb, coeff_mul_top2 c d hc hd]; ring
  · intro i _ hi4; by_cases hgt : 4 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (a * b).natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (c * d).natDegree < 8 - i), mul_zero]
  · intro h; simp at h

private lemma natDegree_mul3_le (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).natDegree ≤ 6 :=
  (Polynomial.natDegree_mul_le).trans (by have := Polynomial.natDegree_mul_le (p := a) (q := b); omega)

private lemma natDegree_mul4_le (a b c d : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2) : (a * b * c * d).natDegree ≤ 8 :=
  (Polynomial.natDegree_mul_le).trans (by have := natDegree_mul3_le a b c ha hb hc; omega)

/-- Exact upper bound `Q5_z.natDegree ≤ 5` over `K5[X]`. -/
lemma k5Params_Q5_z_natDegree_le : k5Params.Q5_z.natDegree ≤ 5 := by
  have htop : (k5Params.q20.coeff 2 * k5Params.cb_h.coeff 2 ^ 2 -
      k5Params.q11.coeff 2 * k5Params.ca_h.coeff 2 * k5Params.cb_h.coeff 2 +
      k5Params.q02.coeff 2 * k5Params.ca_h.coeff 2 ^ 2) = 0 := by
    simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h,
      CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
      CoverParams.inv81, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    simp; ring
  have hle6 : k5Params.Q5_z.natDegree ≤ 6 := by
    rw [CoverParams.Q5_z]
    have h1 : (k5Params.q20 * k5Params.cb_h ^ 2).natDegree ≤ 6 := by
      rw [sq, ← mul_assoc]; exact natDegree_mul3_le _ _ _ deg2_q20 deg2_cb deg2_cb
    have h2 : (k5Params.q11 * k5Params.ca_h * k5Params.cb_h).natDegree ≤ 6 :=
      natDegree_mul3_le _ _ _ deg2_q11 deg2_ca deg2_cb
    have h3 : (k5Params.q02 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
      rw [sq, ← mul_assoc]; exact natDegree_mul3_le _ _ _ deg2_q02 deg2_ca deg2_ca
    exact (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)) h3)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h6 : n = 6
  · subst h6
    rw [CoverParams.Q5_z, Polynomial.coeff_add, Polynomial.coeff_sub, sq, ← mul_assoc, sq, ← mul_assoc,
      coeff_mul_top3 _ _ _ deg2_q20 deg2_cb deg2_cb,
      coeff_mul_top3 _ _ _ deg2_q11 deg2_ca deg2_cb,
      coeff_mul_top3 _ _ _ deg2_q02 deg2_ca deg2_ca]
    linear_combination htop
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- Exact upper bound `Q7_z.natDegree ≤ 7` over `K5[X]`. -/
lemma k5Params_Q7_z_natDegree_le : k5Params.Q7_z.natDegree ≤ 7 := by
  have htop : (k5Params.c30.coeff 2 * k5Params.cb_h.coeff 2 ^ 3 -
      k5Params.c21.coeff 2 * k5Params.ca_h.coeff 2 * k5Params.cb_h.coeff 2 ^ 2 +
      k5Params.c12.coeff 2 * k5Params.ca_h.coeff 2 ^ 2 * k5Params.cb_h.coeff 2 -
      k5Params.c03.coeff 2 * k5Params.ca_h.coeff 2 ^ 3) = 0 := by
    simp only [CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9,
      CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
      Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    simp; ring
  have hle8 : k5Params.Q7_z.natDegree ≤ 8 := by
    rw [CoverParams.Q7_z]
    have h1 : (k5Params.c30 * k5Params.cb_h ^ 3).natDegree ≤ 8 := by
      rw [show k5Params.c30 * k5Params.cb_h ^ 3 = k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h by ring]
      exact natDegree_mul4_le _ _ _ _ deg2_c30 deg2_cb deg2_cb deg2_cb
    have h2 : (k5Params.c21 * k5Params.ca_h * k5Params.cb_h ^ 2).natDegree ≤ 8 := by
      rw [show k5Params.c21 * k5Params.ca_h * k5Params.cb_h ^ 2 = k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h by ring]
      exact natDegree_mul4_le _ _ _ _ deg2_c21 deg2_ca deg2_cb deg2_cb
    have h3 : (k5Params.c12 * k5Params.ca_h ^ 2 * k5Params.cb_h).natDegree ≤ 8 := by
      rw [show k5Params.c12 * k5Params.ca_h ^ 2 * k5Params.cb_h = k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h by ring]
      exact natDegree_mul4_le _ _ _ _ deg2_c12 deg2_ca deg2_ca deg2_cb
    have h4 : (k5Params.c03 * k5Params.ca_h ^ 3).natDegree ≤ 8 := by
      rw [show k5Params.c03 * k5Params.ca_h ^ 3 = k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h by ring]
      exact natDegree_mul4_le _ _ _ _ deg2_c03 deg2_ca deg2_ca deg2_ca
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)) h3)) h4)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h8 : n = 8
  · subst h8
    rw [CoverParams.Q7_z, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub,
      show k5Params.c30 * k5Params.cb_h ^ 3 = k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h by ring,
      show k5Params.c21 * k5Params.ca_h * k5Params.cb_h ^ 2 = k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h by ring,
      show k5Params.c12 * k5Params.ca_h ^ 2 * k5Params.cb_h = k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h by ring,
      show k5Params.c03 * k5Params.ca_h ^ 3 = k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h by ring,
      coeff_mul_top4 _ _ _ _ deg2_c30 deg2_cb deg2_cb deg2_cb,
      coeff_mul_top4 _ _ _ _ deg2_c21 deg2_ca deg2_cb deg2_cb,
      coeff_mul_top4 _ _ _ _ deg2_c12 deg2_ca deg2_ca deg2_cb,
      coeff_mul_top4 _ _ _ _ deg2_c03 deg2_ca deg2_ca deg2_ca]
    linear_combination htop
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- Exact upper bound `nm_z.natDegree ≤ 73` over `K5[X]`, proved via `deg_1 = 32` on `W1_inf`
and `deg_2 = 41` on `W2_inf` (`32 + 41 = 73`). -/
lemma nm_z_K5_natDegree_le : k5Params.nm_z.natDegree ≤ 73 := by
  apply natDegree_le_of_HasValGe_evalInvT
  have hnm : evalInvT k5Params.nm_z =
      PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z) *
      PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_inf W2_inf W1_W2_inf_sum W1_W2_inf_prod _
  rw [hnm]
  have hq02 : HasValGe (-2) (evalInvT k5Params.q02) := HasValGe.evalInvT_of_natDegree_le _ deg2_q02
  have hc03 : HasValGe (-2) (evalInvT k5Params.c03) := HasValGe.evalInvT_of_natDegree_le _ deg2_c03
  have hcb : HasValGe (-2) (evalInvT k5Params.cb_h) := HasValGe.evalInvT_of_natDegree_le _ deg2_cb
  have hQ5 : HasValGe (-5) (evalInvT k5Params.Q5_z) :=
    HasValGe.evalInvT_of_natDegree_le _ k5Params_Q5_z_natDegree_le
  have hQ7 : HasValGe (-7) (evalInvT k5Params.Q7_z) :=
    HasValGe.evalInvT_of_natDegree_le _ k5Params_Q7_z_natDegree_le
  have hcoeff_deg3 (p3 : K5[X]) (hle : p3.natDegree ≤ 4) (h4 : p3.coeff 4 = 0) :
      HasValGe (-3) (evalInvT p3) := by
    apply HasValGe.evalInvT_of_natDegree_le (d := 3)
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_cases h4' : n = 4
    · subst h4'; exact h4
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hd2_1_sc : HasValGe (-3) (evalInvT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h)) := by
    apply hcoeff_deg3
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_neg]; linarith [deg2_q11, deg2_cb])
      · rw [mul_assoc, show (2 : K5[X]) = C 2 from (map_ofNat C 2).symm]
        exact (Polynomial.natDegree_C_mul_le 2 _).trans ((Polynomial.natDegree_mul_le).trans (by linarith [deg2_q02, deg2_ca]))
    · rw [Polynomial.coeff_add, neg_mul, Polynomial.coeff_neg, mul_assoc,
        show (2 : K5[X]) * (k5Params.q02 * k5Params.ca_h) = C 2 * (k5Params.q02 * k5Params.ca_h) by rw [map_ofNat],
        Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_q11 deg2_cb, coeff_mul_top2 _ _ deg2_q02 deg2_ca]
      simp only [CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
        CoverParams.quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C]
      simp; ring
  have hd3_1_sc : HasValGe (-3) (evalInvT (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h)) := by
    apply hcoeff_deg3
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_mul_le).trans (by linarith [deg2_c12, deg2_cb])
      · rw [mul_assoc, show (3 : K5[X]) = C 3 from (map_ofNat C 3).symm]
        exact (Polynomial.natDegree_C_mul_le 3 _).trans ((Polynomial.natDegree_mul_le).trans (by linarith [deg2_c03, deg2_ca]))
    · rw [Polynomial.coeff_sub, mul_assoc,
        show (3 : K5[X]) * (k5Params.c03 * k5Params.ca_h) = C 3 * (k5Params.c03 * k5Params.ca_h) by rw [map_ofNat],
        Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_c12 deg2_cb, coeff_mul_top2 _ _ deg2_c03 deg2_ca]
      simp only [CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
        CoverParams.quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C]
      simp; ring
  have hd3_2_sc : HasValGe (-5) (evalInvT (-k5Params.c21 * k5Params.cb_h ^ 2 +
      2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2)) := by
    apply HasValGe.evalInvT_of_natDegree_le (d := 5)
    have hle6 : (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
        3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
      have h1 : (-k5Params.c21 * k5Params.cb_h ^ 2).natDegree ≤ 6 := by
        rw [show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
          Polynomial.natDegree_neg]
        exact natDegree_mul3_le _ _ _ deg2_c21 deg2_cb deg2_cb
      have h2 : (2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h).natDegree ≤ 6 := by
        rw [show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring]
        exact (Polynomial.natDegree_C_mul_le 2 _).trans (natDegree_mul3_le _ _ _ deg2_c12 deg2_ca deg2_cb)
      have h3 : (3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
        rw [show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring]
        exact (Polynomial.natDegree_C_mul_le 3 _).trans (natDegree_mul3_le _ _ _ deg2_c03 deg2_ca deg2_ca)
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)) h3)
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_cases h6 : n = 6
    · subst h6
      rw [Polynomial.coeff_sub, Polynomial.coeff_add,
        show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
        show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring,
        show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring,
        Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        coeff_mul_top3 _ _ _ deg2_c21 deg2_cb deg2_cb,
        coeff_mul_top3 _ _ _ deg2_c12 deg2_ca deg2_cb,
        coeff_mul_top3 _ _ _ deg2_c03 deg2_ca deg2_ca]
      simp only [CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
        CoverParams.quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C]
      simp; ring
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : HasValGe (-32 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)) := by
    have hw := HasValGe_W1_inf
    have hw_eq := W1_inf_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W1_inf hw_eq]
    have htoUW_1 (v0 v1 v2 : K5) :
        HasValGe (-2 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) := by
      have heq : PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
          HahnSeries.C v2 * W1_inf ^ 2 + HahnSeries.C v1 * HahnSeries.single (-1) 1 * W1_inf +
          HahnSeries.C v0 * HahnSeries.single (-2) 1 := by
        simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
          evalInvT_C, evalInvT_X, HahnSeries.single_pow]
        have h2' : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
        simp only [one_pow, h2']
        linear_combination -HahnSeries.C v2 * hw_eq
      rw [heq]
      have ha := ((HasValGe.of_C v2).mul (hw.pow 2)).mono (by omega : (-2 : ℤ) ≤ 0 + 2 * 0)
      have hb := (((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul hw).mono (by omega : (-2 : ℤ) ≤ 0 + -1 + 0)
      have hc := ((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega : (-2 : ℤ) ≤ 0 + -2)
      exact (ha.add hb).add hc
    have hc0W : HasValGe (-2 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.c0W)) :=
      htoUW_1 k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    have hk2W : HasValGe (-2 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k2W)) :=
      htoUW_1 k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    have hk3W : HasValGe (-2 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k3W)) :=
      htoUW_1 k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    have hq2 : HasValGe (-5 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)) := by
      simpa [CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5
    have hq1 : HasValGe (-5 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)) := by
      rw [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd2_1_sc.mul hc0W).mono (by omega)
    have hq0 : HasValGe (-6 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)) := by
      rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_inf hw_eq,
        PairAlg.evalAt_mul _ _ W1_inf hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      exact ((hq02.mul (hc0W.mul hc0W)).mono (by omega)).add
        (((hcb.pow 2).mul (hw.mul hk2W)).mono (by omega))
    have he3 : HasValGe (-7 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ7
    have he2 : HasValGe (-7 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
      rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd3_2_sc.mul hc0W).mono (by omega)
    have he1 : HasValGe (-7 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
      rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_inf hw_eq]
      exact (hd3_1_sc.mul (hc0W.mul hc0W)).mono (by omega)
    have he0 : HasValGe (-8 : ℤ) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
      rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_inf hw_eq, PairAlg.evalAt_mul _ _ W1_inf hw_eq,
        PairAlg.evalAt_mul _ _ W1_inf hw_eq, PairAlg.evalAt_mul _ _ W1_inf hw_eq, PairAlg.map_W,
        PairAlg.evalAt_W, map_neg, map_pow]
      exact ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)).add
        (((hcb.pow 3).mul ((hw.mul hw).mul hk3W)).mono (by omega))
    exact HasValGe.syl5 hq2 hq1 hq0 he3 he2 he1 he0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 : HasValGe (-41 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) := by
    have hw := HasValGe_W2_inf
    have hw_eq := W2_inf_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_inf hw_eq]
    have hw_c : W2_inf.coeff (-2) = -(k5Params.Bv2 * k5Params.Av0_inv) := by
      rw [W2_inf, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_inf (-2) (by omega), sub_zero,
        evalInvT_bW_eq]
      have hmul := (HasValGe.single (-2 : ℤ) (1 : K5)).coeff_mul_min (HasValGe.of_powerSeries bInfPS)
      simp only [add_zero] at hmul
      rw [hmul, HahnSeries.coeff_single_same, one_mul]
      change -(HahnSeries.coeff ((bInfPS : PowerSeries K5) : LaurentSeries K5) (0 : ℕ)) = _
      rw [LaurentSeries.coeff_coe_powerSeries, bInfPS_coeff0]
    have htoUW_c (v0 v1 v2 : K5) :
        HasValGe (-4 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) ∧
        (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))).coeff (-4) =
          v2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2 := by
      have heq : PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
          HahnSeries.C v2 * W2_inf ^ 2 +
          (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf +
           HahnSeries.C v0 * HahnSeries.single (-2) 1) := by
        simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
          evalInvT_C, evalInvT_X, HahnSeries.single_pow]
        have h2' : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
        simp only [one_pow, h2']
        linear_combination -HahnSeries.C v2 * hw_eq
      have ht1 : HasValGe (-4 : ℤ) (HahnSeries.C v2 * W2_inf ^ 2) :=
        ((HasValGe.of_C v2).mul (hw.pow 2)).mono (by omega)
      have ht2 : HasValGe (-3 : ℤ) (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf +
          HahnSeries.C v0 * HahnSeries.single (-2) 1) :=
        ((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul hw).mono (by omega)).add
          (((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega))
      rw [heq]
      refine ⟨ht1.add (ht2.mono (by omega)), ?_⟩
      rw [HasValGe.coeff_of_add ht2]
      have hm := (HasValGe.of_C v2).coeff_mul_min (hw.pow 2)
      simp only [zero_add] at hm
      change (HahnSeries.C v2 * W2_inf ^ 2).coeff ((2 : ℕ) * (-2 : ℤ)) = _
      rw [hm, HahnSeries.C_apply, HahnSeries.coeff_single_same, hw.coeff_pow_min 2, hw_c]
    obtain ⟨hc0W, hc0W_c⟩ : HasValGe (-4 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.c0W)) ∧
        (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.c0W)).coeff (-4) =
          k5Params.c0_V2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_c k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    obtain ⟨hk2W, hk2W_c⟩ : HasValGe (-4 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.k2W)) ∧
        (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.k2W)).coeff (-4) =
          k5Params.k2_V2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_c k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    obtain ⟨hk3W, hk3W_c⟩ : HasValGe (-4 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.k3W)) ∧
        (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.k3W)).coeff (-4) =
          k5Params.k3_V2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_c k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    have hq2 : HasValGe (-5 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_2)) := by
      simpa [CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5
    have hq1 : HasValGe (-7 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_1)) := by
      rw [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd2_1_sc.mul hc0W).mono (by omega)
    have hq0_10 : HasValGe (-10 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)) := by
      rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      exact ((hq02.mul (hc0W.mul hc0W)).mono (by omega)).add
        (((hcb.pow 2).mul (hw.mul hk2W)).mono (by omega))
    have hq0 : HasValGe (-9 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)) := by
      apply hq0_10.inc
      rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow,
        HahnSeries.coeff_add]
      have h10a := hq02.coeff_mul_min (hc0W.mul hc0W)
      have h10b := (hcb.pow 2).coeff_mul_min (hw.mul hk2W)
      rw [show (-10 : ℤ) = -2 + (-4 + -4) by norm_num, h10a, hc0W.coeff_mul_min hc0W]
      rw [show (-2 + (-4 + -4) : ℤ) = (2 : ℕ) * (-2 : ℤ) + (-2 + -4) by norm_num, h10b,
        hcb.coeff_pow_min 2, hw.coeff_mul_min hk2W, hw_c,
        show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
        evalInvT_coeff_neg, evalInvT_coeff_neg, hc0W_c, hk2W_c]
      simp only [CoverParams.q02, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, CoverParams.quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      simp only [Nat.reduceEqDiff, ↓reduceIte, mul_zero, zero_add, add_zero, mul_one]
      have hT := T_K_sub_3_ne
      field_simp [hT]; ring
    have he3 : HasValGe (-7 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ7
    have he2 : HasValGe (-9 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
      rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd3_2_sc.mul hc0W).mono (by omega)
    have he1 : HasValGe (-11 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
      rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq]
      exact (hd3_1_sc.mul (hc0W.mul hc0W)).mono (by omega)
    have he0_14 : HasValGe (-14 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
      rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W,
        PairAlg.evalAt_W, map_neg, map_pow]
      exact ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)).add
        (((hcb.pow 3).mul ((hw.mul hw).mul hk3W)).mono (by omega))
    have he0 : HasValGe (-13 : ℤ) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
      apply he0_14.inc
      rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W,
        PairAlg.evalAt_W, map_neg, map_pow, HahnSeries.coeff_add]
      have h14a := hc03.neg.coeff_mul_min (hc0W.mul (hc0W.mul hc0W))
      have h14b := (hcb.pow 3).coeff_mul_min ((hw.mul hw).mul hk3W)
      rw [show (-14 : ℤ) = -2 + (-4 + (-4 + -4)) by norm_num, h14a,
        hc0W.coeff_mul_min (hc0W.mul hc0W), hc0W.coeff_mul_min hc0W, HahnSeries.coeff_neg]
      rw [show (-2 + (-4 + (-4 + -4)) : ℤ) = (3 : ℕ) * (-2 : ℤ) + (-2 + -2 + -4) by norm_num, h14b,
        hcb.coeff_pow_min 3, (hw.mul hw).coeff_mul_min hk3W, hw.coeff_mul_min hw, hw_c,
        show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
        evalInvT_coeff_neg, evalInvT_coeff_neg, hc0W_c, hk3W_c]
      simp only [CoverParams.c03, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k3_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, CoverParams.quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      simp only [Nat.reduceEqDiff, ↓reduceIte, mul_zero, zero_add, add_zero, mul_one]
      have hT := T_K_sub_3_ne
      field_simp [hT]; ring
    exact HasValGe.syl5 hq2 hq1 hq0 he3 he2 he1 he0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact (h1.mul h2).mono (by omega)

end CoverDegBounds
end SymmetricSexticResidual.CoverAlgebra

theorem solution :
    SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z.natDegree ≤ 5 ∧
    SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z.natDegree ≤ 7 ∧
    SymmetricSexticResidual.CoverAlgebra.k5Params.nm_z.natDegree ≤ 73 :=
  ⟨SymmetricSexticResidual.CoverAlgebra.k5Params_Q5_z_natDegree_le,
   SymmetricSexticResidual.CoverAlgebra.k5Params_Q7_z_natDegree_le,
   SymmetricSexticResidual.CoverAlgebra.nm_z_K5_natDegree_le⟩
