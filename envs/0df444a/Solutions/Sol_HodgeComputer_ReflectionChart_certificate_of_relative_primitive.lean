-- Prove2me | solution 1 for HodgeComputer.ReflectionChart.certificate_of_relative_primitive
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:58:00.394254+00:00
-- url     : https://prove2.me/submissions/5d6838f1-7f0b-40a2-80d9-9dc0d9345b25

import Definitions.Def_HodgeComputerReflectionChart
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Prime.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace ReflectionChartTransport

open MvPolynomial HodgeComputer HodgeComputer.ReflectionChart
open scoped BigOperators

/-! ### 1. Even-degree projection and divisibility under `squareLift` -/

private def doubleLast (d : Fin 5 →₀ ℕ) : Fin 5 →₀ ℕ :=
  d + Finsupp.single 4 (d 4)

private lemma doubleLast_add (d₁ d₂ : Fin 5 →₀ ℕ) :
    doubleLast (d₁ + d₂) = doubleLast d₁ + doubleLast d₂ := by
  ext i
  simp only [doubleLast, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

private lemma doubleLast_injective : Function.Injective doubleLast := by
  intro d₁ d₂ h
  ext i
  have hi := Finsupp.ext_iff.mp h i
  simp only [doubleLast, Finsupp.add_apply, Finsupp.single_apply] at hi
  by_cases h4 : i = 4
  · subst h4; simp at hi; omega
  · have h4' : (4 : Fin 5) ≠ i := Ne.symm h4
    simpa [h4'] using hi

private lemma squareLift_monomial (d : Fin 5 →₀ ℕ) (c : ℂ) :
    squareLift (monomial d c) = monomial (doubleLast d) c := by
  rw [squareLift, eval₂Hom_monomial]
  have hprod : (∏ i ∈ d.support, (if i = (4 : Fin 5) then X i ^ 2 else (X i : ChartPoly)) ^ d i) =
      monomial (doubleLast d) 1 := by
    induction d using Finsupp.induction with
    | zero =>
      have h0 : doubleLast 0 = 0 := by ext i; simp [doubleLast]
      simp [h0]
    | single_add a b f ha hb ih =>
      rw [Finsupp.support_single_add ha hb, Finset.prod_cons]
      have hrest : (∏ x ∈ f.support, (if x = (4 : Fin 5) then X x ^ 2 else (X x : ChartPoly)) ^
          (Finsupp.single a b + f) x) =
          ∏ x ∈ f.support, (if x = (4 : Fin 5) then X x ^ 2 else (X x : ChartPoly)) ^ f x := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxa : a ≠ x := fun h => ha (h ▸ hx)
        simp [Finsupp.single_apply, hxa]
      have hhead : (Finsupp.single a b + f) a = b := by
        simp [Finsupp.notMem_support_iff.mp ha]
      rw [hrest, hhead, ih, doubleLast_add]
      by_cases ha4 : a = 4
      · subst ha4
        have hdl : doubleLast (Finsupp.single 4 b) = Finsupp.single 4 (2 * b) := by
          ext i; simp [doubleLast, Finsupp.single_apply]; split_ifs <;> omega
        rw [if_pos rfl, ← pow_mul, X_pow_eq_monomial, hdl, monomial_mul, one_mul]
      · have hdl : doubleLast (Finsupp.single a b) = Finsupp.single a b := by
          ext i; simp [doubleLast, Finsupp.single_apply, ha4]
        rw [if_neg ha4, X_pow_eq_monomial, hdl, monomial_mul, one_mul]
  change C c * (∏ i ∈ d.support, (if i = (4 : Fin 5) then X i ^ 2 else (X i : ChartPoly)) ^ d i) = _
  rw [hprod, C_mul_monomial, mul_one]

private lemma coeff_squareLift_doubleLast (p : ChartPoly) (d : Fin 5 →₀ ℕ) :
    coeff (doubleLast d) (squareLift p) = coeff d p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [squareLift_monomial, coeff_monomial, coeff_monomial]
    simp [doubleLast_injective.eq_iff]
  | add p q hp hq =>
    simp [map_add, hp, hq]

private lemma coeff_squareLift_odd (p : ChartPoly) {m : Fin 5 →₀ ℕ} (hm : m 4 % 2 = 1) :
    coeff m (squareLift p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [squareLift_monomial, coeff_monomial]
    have hne : doubleLast d ≠ m := by
      intro h
      have h4 := congrArg (fun x : Fin 5 →₀ ℕ => x 4) h
      simp [doubleLast] at h4
      omega
    simp [hne]
  | add p q hp hq =>
    simp [map_add, hp, hq]

private def halfLast (m : Fin 5 →₀ ℕ) : Fin 5 →₀ ℕ :=
  m.update 4 (m 4 / 2)

private lemma doubleLast_halfLast {m : Fin 5 →₀ ℕ} (hm : m 4 % 2 = 0) :
    doubleLast (halfLast m) = m := by
  ext i
  by_cases hi : i = 4
  · subst hi; simp [doubleLast, halfLast]; omega
  · simp [doubleLast, halfLast, hi]

private lemma halfLast_doubleLast (d : Fin 5 →₀ ℕ) :
    halfLast (doubleLast d) = d := by
  ext i
  by_cases hi : i = 4
  · subst hi; simp [doubleLast, halfLast]; omega
  · simp [doubleLast, halfLast, hi]

private def evenProj (q : ChartPoly) : ChartPoly :=
  ∑ d ∈ q.support.image halfLast, monomial d (coeff (doubleLast d) q)

private lemma coeff_evenProj (q : ChartPoly) (d : Fin 5 →₀ ℕ) :
    coeff d (evenProj q) = coeff (doubleLast d) q := by
  simp only [evenProj, coeff_sum, coeff_monomial]
  by_cases hmem : d ∈ q.support.image halfLast
  · rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hbd; simp [hbd]
    · intro hnot; exact absurd hmem hnot
  · rw [Finset.sum_eq_zero (fun x hx => if_neg (by rintro rfl; exact hmem hx))]
    by_contra hne
    apply hmem
    exact Finset.mem_image.mpr ⟨doubleLast d, mem_support_iff.mpr (Ne.symm hne), halfLast_doubleLast d⟩

private lemma evenProj_squareLift (D : ChartPoly) : evenProj (squareLift D) = D := by
  ext d
  rw [coeff_evenProj, coeff_squareLift_doubleLast]

private lemma evenProj_mul_squareLift (a g : ChartPoly) :
    evenProj (squareLift a * g) = a * evenProj g := by
  ext d
  rw [coeff_evenProj, coeff_mul, coeff_mul]
  let emb : (Fin 5 →₀ ℕ) × (Fin 5 →₀ ℕ) ↪ (Fin 5 →₀ ℕ) × (Fin 5 →₀ ℕ) :=
    ⟨fun p => (doubleLast p.1, doubleLast p.2), fun p₁ p₂ h =>
      Prod.ext (doubleLast_injective (congrArg Prod.fst h))
        (doubleLast_injective (congrArg Prod.snd h))⟩
  have hsub : (Finset.antidiagonal d).map emb ⊆ Finset.antidiagonal (doubleLast d) := by
    intro uv huv
    rcases Finset.mem_map.mp huv with ⟨ab, hab, rfl⟩
    rw [Finset.mem_antidiagonal] at hab ⊢
    change doubleLast ab.1 + doubleLast ab.2 = doubleLast d
    rw [← doubleLast_add, hab]
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro ab _
    change coeff (doubleLast ab.1) (squareLift a) * coeff (doubleLast ab.2) g = _
    rw [coeff_squareLift_doubleLast, coeff_evenProj]
  · intro uv huv hnot
    by_cases hodd : uv.1 4 % 2 = 1
    · rw [coeff_squareLift_odd a hodd, zero_mul]
    · exfalso
      have hev1 : uv.1 4 % 2 = 0 := by omega
      rw [Finset.mem_antidiagonal] at huv
      have h4 := congrArg (fun x : Fin 5 →₀ ℕ => x 4) huv
      simp only [Finsupp.add_apply, doubleLast, Finsupp.single_apply, ↓reduceIte] at h4
      have hev2 : uv.2 4 % 2 = 0 := by omega
      apply hnot
      refine Finset.mem_map.mpr ⟨(halfLast uv.1, halfLast uv.2), ?_, ?_⟩
      · rw [Finset.mem_antidiagonal]
        apply doubleLast_injective
        rw [doubleLast_add, doubleLast_halfLast hev1, doubleLast_halfLast hev2, huv]
      · change (doubleLast (halfLast uv.1), doubleLast (halfLast uv.2)) = uv
        rw [doubleLast_halfLast hev1, doubleLast_halfLast hev2]

private lemma not_squareLift_dvd_of_not_dvd {f D : ChartPoly} (h : ¬ f ∣ D) :
    ¬ squareLift f ∣ squareLift D := by
  rintro ⟨g, hg⟩
  apply h
  refine ⟨evenProj g, ?_⟩
  have h1 := congrArg evenProj hg
  rw [evenProj_squareLift, evenProj_mul_squareLift] at h1
  exact h1

/-! ### 2. Cleared affine residue identity on the 5-variable reflection chart -/

private lemma normal_squareLift (p : ChartPoly) :
    pderiv 4 (squareLift p) = C 2 * X 4 * squareLift (pderiv 4 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [squareLift, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
    by_cases hj : j = 4
    · subst hj
      have hX4 : squareLift (X 4) = X 4 ^ 2 := by simp [squareLift]
      simp only [map_mul, hX4, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
        smul_eq_mul, hp, map_add, map_one, map_ofNat, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    · have hXj : squareLift (X j) = X j := by simp [squareLift, hj]
      simp only [map_mul, hXj, Derivation.leibniz, pderiv_X_of_ne hj, hp, smul_eq_mul,
        mul_zero, zero_add, add_zero]
      ring

private lemma tangent_squareLift (i : Fin 4) (p : ChartPoly) :
    pderiv i.castSucc (squareLift p) = squareLift (pderiv i.castSucc p) := by
  have hi : i.castSucc ≠ (4 : Fin 5) := Fin.castSucc_ne_last i
  induction p using MvPolynomial.induction_on with
  | C r => simp [squareLift, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 4
    · subst hj
      have hX4 : squareLift (X 4) = X 4 ^ 2 := by simp [squareLift]
      simp [map_mul, hX4, Derivation.leibniz, Derivation.leibniz_pow, hp,
        pderiv_X_of_ne hi.symm, hi]
    · have hXj : squareLift (X j) = X j := by simp [squareLift, hj]
      by_cases hji : j = i.castSucc
      · subst hji; simp [map_mul, hXj, Derivation.leibniz, hp, smul_eq_mul]
      · simp [map_mul, hXj, Derivation.leibniz, hp, pderiv_X_of_ne hji, smul_eq_mul]

private lemma pderiv_comm_chart (i j : Fin 5) (p : ChartPoly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ ChartPoly ChartPoly),
      (pderiv j : Derivation ℂ ChartPoly ChartPoly)⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  have hp := DFunLike.congr_fun h p
  exact sub_eq_zero.mp (by simpa only [Derivation.commutator_apply, Derivation.zero_apply] using hp)

private def dirPoly {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℂ)
    (N : σ → MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i, pderiv i P * N i

private def divNumPoly {σ : Type*} [Fintype σ] (D : MvPolynomial σ ℂ)
    (N : σ → MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  D * (∑ i, pderiv i (N i)) - dirPoly D N

private theorem affine_normalized_of_relative_primitive
    (f P : ChartPoly)
    (hH_irred : Irreducible (squareLift f))
    (h_pt_zero : eval normalPoint (squareLift f) = 0)
    (h_pt_fu : eval normalPoint (squareLift (pderiv 4 f)) ≠ 0)
    (h_prim : RelativePrimitive f P) :
    ∃ (D_aff Q_aff : ChartPoly) (N : Fin 5 → ChartPoly),
      D_aff ≠ 0 ∧ IsRelPrime (squareLift f) D_aff ∧
      dirPoly (squareLift f) N = reflectedSource P * D_aff ∧
      divNumPoly D_aff N = squareLift f * Q_aff := by
  obtain ⟨D, Cvec, Q, _, h_coprime, hdefect⟩ := h_prim
  have hH_prime : Prime (squareLift f) := irreducible_iff_prime.mp hH_irred
  have hnot_f_dvd_D : ¬ f ∣ D := by
    intro hfd
    exact hH_irred.not_isUnit ((h_coprime dvd_rfl hfd).map squareLift)
  have hnot_H_dvd_sqD : ¬ squareLift f ∣ squareLift D :=
    not_squareLift_dvd_of_not_dvd hnot_f_dvd_D
  have hnot_H_dvd_sqfu : ¬ squareLift f ∣ squareLift (pderiv 4 f) := by
    intro hdiv
    have hmap := map_dvd (eval normalPoint) hdiv
    rw [h_pt_zero, zero_dvd_iff] at hmap
    exact h_pt_fu hmap
  let fu := pderiv 4 f
  let D_aff : ChartPoly := squareLift (fu * D)
  let Nv : ChartPoly :=
    squareLift (C 2 * P * D + fu * ∑ j : Fin 3, Cvec j * pderiv j.succ.castSucc f)
  let N : Fin 5 → ChartPoly :=
    ![0,
      -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 0)),
      -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 1)),
      -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 2)),
      Nv]
  let Q_aff : ChartPoly := -(C 2 * X 4 * squareLift Q)
  have hnot_H_dvd_Daff : ¬ squareLift f ∣ D_aff := by
    change ¬ squareLift f ∣ squareLift (fu * D)
    rw [map_mul]
    exact hH_prime.not_dvd_mul hnot_H_dvd_sqfu hnot_H_dvd_sqD
  have hDaff_ne : D_aff ≠ 0 := fun hz => hnot_H_dvd_Daff (hz ▸ dvd_zero _)
  have hDaff_legal : IsRelPrime (squareLift f) D_aff :=
    hH_irred.isRelPrime_iff_not_dvd.mpr hnot_H_dvd_Daff
  refine ⟨D_aff, Q_aff, N, hDaff_ne, hDaff_legal, ?_, ?_⟩
  · unfold dirPoly reflectedSource
    simp only [Fin.sum_univ_five, N, Nv, D_aff, Fin.sum_univ_three]
    have ht1 : pderiv 1 (squareLift f) = squareLift (pderiv 1 f) := tangent_squareLift 1 f
    have ht2 : pderiv 2 (squareLift f) = squareLift (pderiv 2 f) := tangent_squareLift 2 f
    have ht3 : pderiv 3 (squareLift f) = squareLift (pderiv 3 f) := tangent_squareLift 3 f
    have hn4 : pderiv 4 (squareLift f) = C 2 * X 4 * squareLift fu := normal_squareLift f
    change pderiv 0 (squareLift f) * 0 +
      pderiv 1 (squareLift f) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 0)) +
      pderiv 2 (squareLift f) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 1)) +
      pderiv 3 (squareLift f) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 2)) +
      pderiv 4 (squareLift f) * squareLift (C 2 * P * D +
        fu * (Cvec 0 * pderiv 1 f + Cvec 1 * pderiv 2 f + Cvec 2 * pderiv 3 f)) =
      C 4 * X 4 * squareLift P * squareLift (fu * D)
    rw [ht1, ht2, ht3, hn4]
    have hc4 : (C (4 : ℂ) : ChartPoly) = C 2 * C 2 := by rw [← map_mul]; norm_num
    have hsqC2 : squareLift (C 2) = C 2 := by simp [squareLift]
    rw [hc4]
    simp only [map_add, map_mul, map_pow, hsqC2]
    ring
  · have hdef_sq := congrArg squareLift hdefect
    unfold cubicResidueDefect at hdef_sq
    simp only [Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hdef_sq
    change squareLift (fu ^ 2 *
        ((fu * (D * pderiv 1 (Cvec 0) - Cvec 0 * pderiv 1 D) -
            pderiv 1 f * (D * pderiv 4 (Cvec 0) - Cvec 0 * pderiv 4 D)) +
          (fu * (D * pderiv 2 (Cvec 1) - Cvec 1 * pderiv 2 D) -
            pderiv 2 f * (D * pderiv 4 (Cvec 1) - Cvec 1 * pderiv 4 D)) +
          (fu * (D * pderiv 3 (Cvec 2) - Cvec 2 * pderiv 3 D) -
            pderiv 3 f * (D * pderiv 4 (Cvec 2) - Cvec 2 * pderiv 4 D))) -
        C 2 * D ^ 2 * (fu * pderiv 4 P - pderiv 4 fu * P)) =
      squareLift (f * Q) at hdef_sq
    have hcomm1 : pderiv 4 (pderiv 1 f) = pderiv 1 fu := pderiv_comm_chart 4 1 f
    have hcomm2 : pderiv 4 (pderiv 2 f) = pderiv 2 fu := pderiv_comm_chart 4 2 f
    have hcomm3 : pderiv 4 (pderiv 3 f) = pderiv 3 fu := pderiv_comm_chart 4 3 f
    unfold divNumPoly dirPoly
    simp only [Fin.sum_univ_five, N, Nv, D_aff, Q_aff, Fin.sum_univ_three]
    change squareLift (fu * D) *
        (pderiv 0 0 +
          pderiv 1 (-(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 0))) +
          pderiv 2 (-(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 1))) +
          pderiv 3 (-(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 2))) +
          pderiv 4 (squareLift (C 2 * P * D +
            fu * (Cvec 0 * pderiv 1 f + Cvec 1 * pderiv 2 f + Cvec 2 * pderiv 3 f)))) -
        (pderiv 0 (squareLift (fu * D)) * 0 +
          pderiv 1 (squareLift (fu * D)) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 0)) +
          pderiv 2 (squareLift (fu * D)) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 1)) +
          pderiv 3 (squareLift (fu * D)) * -(C 2 * X 4 * squareLift (fu ^ 2 * Cvec 2)) +
          pderiv 4 (squareLift (fu * D)) * squareLift (C 2 * P * D +
            fu * (Cvec 0 * pderiv 1 f + Cvec 1 * pderiv 2 f + Cvec 2 * pderiv 3 f))) =
      squareLift f * -(C 2 * X 4 * squareLift Q)
    have hX4_1 : pderiv (1 : Fin 5) (X 4 : ChartPoly) = 0 := pderiv_X_of_ne (by decide)
    have hX4_2 : pderiv (2 : Fin 5) (X 4 : ChartPoly) = 0 := pderiv_X_of_ne (by decide)
    have hX4_3 : pderiv (3 : Fin 5) (X 4 : ChartPoly) = 0 := pderiv_X_of_ne (by decide)
    have ht1_a (q : ChartPoly) : pderiv 1 (squareLift q) = squareLift (pderiv 1 q) := tangent_squareLift 1 q
    have ht2_a (q : ChartPoly) : pderiv 2 (squareLift q) = squareLift (pderiv 2 q) := tangent_squareLift 2 q
    have ht3_a (q : ChartPoly) : pderiv 3 (squareLift q) = squareLift (pderiv 3 q) := tangent_squareLift 3 q
    simp only [map_zero, map_neg, Derivation.leibniz, pderiv_C, hX4_1, hX4_2, hX4_3,
      smul_eq_mul, zero_mul, mul_zero, add_zero, zero_add]
    rw [ht1_a (fu ^ 2 * Cvec 0), ht2_a (fu ^ 2 * Cvec 1), ht3_a (fu ^ 2 * Cvec 2),
      ht1_a (fu * D), ht2_a (fu * D), ht3_a (fu * D),
      normal_squareLift (C 2 * P * D + fu * (Cvec 0 * pderiv 1 f + Cvec 1 * pderiv 2 f + Cvec 2 * pderiv 3 f)),
      normal_squareLift (fu * D)]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat, hcomm1, hcomm2, hcomm3]
    simp only [map_zero, map_sub, map_add, map_mul, map_pow, map_ofNat] at hdef_sq ⊢
    linear_combination -(2 * X 4) * hdef_sq

/-! ### 3. Fraction-field derivations, Piola calculus, and homogeneous clearing -/

section FractionDerivations
variable {P F : Type*} [CommRing P] [IsDomain P] [Field F]
  [Algebra ℚ P] [Algebra P F] [IsFractionRing P F]
  [Algebra ℚ F] [IsScalarTower ℚ P F]

private def numF (x : F) : P := Classical.choose (IsFractionRing.div_surjective P x)
private def denF (x : F) : P := Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective P x))
private lemma denF_mem (x : F) : denF (P := P) x ∈ nonZeroDivisors P :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).1
private lemma reprF_eq (x : F) :
    algebraMap P F (numF x) / algebraMap P F (denF x) = x :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).2
private lemma denF_ne (x : F) : algebraMap P F (denF x) ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (denF_mem x)
private lemma mapF_ne {x : P} (hx : x ≠ 0) : algebraMap P F x ≠ 0 :=
  fun h => hx ((IsFractionRing.injective P F) (by simpa using h))

private def quotientD (D : Derivation ℚ P P) (x : F) : F :=
  (algebraMap P F (D (numF x)) * algebraMap P F (denF x) -
    algebraMap P F (numF x) * algebraMap P F (D (denF x))) /
    algebraMap P F (denF x) ^ 2

private lemma quotientD_div (D : Derivation ℚ P P) (a b : P) (hb : b ≠ 0) :
    quotientD D (algebraMap P F a / algebraMap P F b) =
      (algebraMap P F (D a) * algebraMap P F b -
        algebraMap P F a * algebraMap P F (D b)) / algebraMap P F b ^ 2 := by
  let x := algebraMap P F a / algebraMap P F b
  have hd := denF_ne (P := P) x
  have hb' := mapF_ne (F := F) hb
  have hcross : numF x * b = a * denF x := by
    apply IsFractionRing.injective P F
    simpa only [map_mul] using (div_eq_div_iff hd hb').mp (reprF_eq (P := P) x)
  have hdcross := congrArg (fun p : P => algebraMap P F (D p)) hcross
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hdcross
  have hcross' := congrArg (algebraMap P F) hcross
  simp only [map_mul] at hcross'
  change (algebraMap P F (D (numF x)) * algebraMap P F (denF x) -
    algebraMap P F (numF x) * algebraMap P F (D (denF x))) /
    algebraMap P F (denF x) ^ 2 = _
  field_simp
  linear_combination
    algebraMap P F (denF x) * algebraMap P F b * hdcross -
    (algebraMap P F b * algebraMap P F (D (denF x)) +
      algebraMap P F (denF x) * algebraMap P F (D b)) * hcross'

private lemma quotientD_map (D : Derivation ℚ P P) (a : P) :
    quotientD D (algebraMap P F a) = algebraMap P F (D a) := by
  simpa using quotientD_div (F := F) D a 1 one_ne_zero

private lemma quotientD_add (D : Derivation ℚ P P) (x y : F) :
    quotientD D (x + y) = quotientD D x + quotientD D y := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := mapF_ne (F := F) hb0
  have hd' := mapF_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b + algebraMap P F c / algebraMap P F d =
      algebraMap P F (a * d + c * b) / algebraMap P F (b * d) := by
    simp only [map_add, map_mul]; field_simp
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0, quotientD_div D _ _ hd0]
  simp only [map_add, map_mul, Derivation.leibniz, smul_eq_mul]
  field_simp <;> ring

private lemma quotientD_mul (D : Derivation ℚ P P) (x y : F) :
    quotientD D (x * y) = x * quotientD D y + y * quotientD D x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := mapF_ne (F := F) hb0
  have hd' := mapF_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b * (algebraMap P F c / algebraMap P F d) =
      algebraMap P F (a * c) / algebraMap P F (b * d) := by
    simp only [map_mul, mul_div_mul_comm]
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0, quotientD_div D _ _ hd0]
  simp only [map_mul, Derivation.leibniz, map_add, smul_eq_mul]
  field_simp <;> ring

private def extendFrac (D : Derivation ℚ P P) : Derivation ℚ F F :=
  Derivation.mk'
    ({ toFun := quotientD D
       map_zero' := by simpa using quotientD_map (F := F) D 0
       map_add' := quotientD_add D } : F →+ F).toRatLinearMap
    (fun x y => quotientD_mul D x y)

@[simp] private lemma extendFrac_map (D : Derivation ℚ P P) (a : P) :
    extendFrac (F := F) D (algebraMap P F a) = algebraMap P F (D a) :=
  quotientD_map D a
end FractionDerivations

section ChainAndPiola
private lemma derivation_eval₂_chain {R L σ : Type*} [CommRing R] [Field L]
    [Fintype σ] [DecidableEq σ]
    (D : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r) = 0) (p : MvPolynomial σ R) :
    D (eval₂Hom φ x p) = ∑ i, eval₂Hom φ x (pderiv i p) * D (x i) := by
  let θ := eval₂Hom φ x
  change D (θ p) = ∑ i, θ (pderiv i p) * D (x i)
  induction p using MvPolynomial.induction_on with
  | C r => simp [θ, hC]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz]
    simp only [θ, eval₂Hom_X', smul_eq_mul] at hp ⊢
    rw [hp]
    simp only [pderiv_mul, map_add, map_mul, eval₂Hom_X', add_mul, Finset.sum_add_distrib]
    have hsum : (∑ i, eval₂Hom φ x (pderiv i p) * x j * D (x i)) =
        x j * (∑ i, eval₂Hom φ x (pderiv i p) * D (x i)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum]
    have hdelta : (∑ i, eval₂Hom φ x p * eval₂Hom φ x (pderiv i (X j)) * D (x i)) =
        eval₂Hom φ x p * D (x j) := by
      simp [pderiv_X, Pi.single_apply, apply_ite, mul_ite, ite_mul]
    rw [hdelta]; ring

private lemma pderiv_degree_lt {k σ : Type*} [Field k] [CharZero k] [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ k) (i : σ) (hp : 0 < p.totalDegree) :
    (pderiv i p).totalDegree < p.totalDegree := by
  rw [totalDegree, Finset.sup_lt_iff hp]
  intro m hm
  have hcoeff : coeff (m + Finsupp.single i 1) p ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hs : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index] <;> simp
  rw [hs] at hd
  omega

private lemma constant_of_partials_zero {k σ : Type*} [Field k] [CharZero k]
    [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ k) (h : ∀ i, pderiv i p = 0) :
    p = C (coeff 0 p) := by
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · rw [coeff_C, if_neg (Ne.symm hm)]
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra! hn; exact hm (Finsupp.ext hn)
    have hs : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
      Finsupp.sub_add_single_one_cancel hi
    have hc := congrArg (coeff (m - Finsupp.single i 1)) (h i)
    rw [coeff_pderiv, hs, coeff_zero] at hc
    have hz : (((m - Finsupp.single i 1 : σ →₀ ℕ) i) : k) + 1 ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    exact (mul_eq_zero.mp hc).resolve_right hz

private lemma injective_of_coordinate_derivations {k K σ : Type*} [Field k] [Field K]
    [CharZero k] [Fintype σ] [DecidableEq σ]
    (φ : k →+* K) (x : σ → K) (D : σ → Derivation ℤ K K)
    (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if j = i then 1 else 0) :
    Function.Injective (eval₂Hom φ x) := by
  let ρ := eval₂Hom φ x
  have hcomp : ∀ i p, D i (ρ p) = ρ (pderiv i p) := by
    intro i p
    rw [derivation_eval₂_chain (D i) φ x (hC i) p]
    simp [ρ, hx]
  have hz : ∀ p : MvPolynomial σ k, ρ p = 0 → p = 0 := by
    intro p
    induction hn : p.totalDegree using Nat.strong_induction_on generalizing p with
    | h n ih =>
      intro hzero
      have hconst : p = C (coeff 0 p) := by
        by_cases hn0 : n = 0
        · exact totalDegree_eq_zero_iff_eq_C.mp (hn.trans hn0)
        · apply constant_of_partials_zero
          intro i
          apply ih (pderiv i p).totalDegree
          · rw [← hn]; exact pderiv_degree_lt p i (by omega)
          · rfl
          · rw [← hcomp, hzero, map_zero]
      rw [hconst, eval₂Hom_C] at hzero
      have hc : coeff 0 p = 0 := φ.injective (by simpa using hzero)
      rw [hconst, hc, map_zero]
  exact (injective_iff_map_eq_zero ρ).mpr hz

private lemma derivation_prod_update {R ι : Type*} [CommRing R] [DecidableEq ι]
    (D : Derivation ℤ R R) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    have hfirst : (∏ j ∈ insert a s, Function.update f a (D (f a)) j) =
        D (f a) * ∏ j ∈ s, f j := by
      rw [Finset.prod_insert ha, Function.update_self, Finset.prod_update_of_notMem ha]
    rw [hfirst, add_comm]
    congr 1
    · exact mul_comm _ _
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.prod_insert ha, Function.update_of_ne hai]

private lemma derivation_det_inverse {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (D : Derivation ℤ R R) (M N : Matrix ι ι R) (hMN : M * N = 1) :
    D M.det = M.det * ∑ i, ∑ j, N i j * D (M j i) := by
  have hcols : D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
    simp only [Matrix.det_apply', map_sum, D.leibniz, D.map_intCast,
      smul_eq_mul, mul_zero, add_zero, derivation_prod_update, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro σ _
    congr 1; apply Finset.prod_congr rfl; intro j _
    by_cases h : j = i
    · subst j; simp
    · simp [Matrix.updateCol, h]
  rw [hcols, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcol : (fun j => D (M j i)) = fun j => ∑ k, (∑ l, N k l * D (M l i)) * M j k := by
    have hh := Matrix.mulVec_mulVec (fun j => D (M j i)) M N
    rw [hMN, Matrix.one_mulVec] at hh
    ext j
    have hj := congrFun hh j
    simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm] using hj.symm
  rw [hcol]
  simpa only [smul_eq_mul, mul_comm] using
    (Matrix.det_updateCol_sum M i (fun k => ∑ l, N k l * D (M l i)))

private def fieldDiv {K ι : Type*} [Field K] [Fintype ι] (D : ι → Derivation ℤ K K) (v : ι → K) : K :=
  ∑ i, D i (v i)

private lemma column_directional {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K) (hNM : N * M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x) (i : ι) (x : K) :
    ∑ j, M j i * E j x = D i x := by
  simp_rw [chain, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ k, (∑ j, M j i * (N k j * D k x)) = (N * M) k i * D k x := by
    intro k; simp only [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [hinner, hNM]
  simp [Matrix.one_apply]

private lemma piola_contraction {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z) (u : ι → K) (f : K) :
    (∑ j, (∑ i, (u i / M.det) * M j i) * E j f) = (∑ i, u i * D i f) / M.det := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, column_directional D E M N hNM chain]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; ring

private lemma piola_divergence {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M * N = 1) (hNM : N * M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (w : ι → K) :
    fieldDiv E (fun j => ∑ i, (w i / M.det) * M j i) = fieldDiv D w / M.det := by
  have hsmul : ∀ (a : K) (v : ι → K),
      fieldDiv E (fun j => a * v j) = (∑ j, v j * E j a) + a * fieldDiv E v := by
    intro a v
    simp only [fieldDiv, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hsum : ∀ (v : ι → ι → K),
      fieldDiv E (fun j => ∑ i, v i j) = ∑ i, fieldDiv E (v i) := by
    intro v; simp only [fieldDiv, map_sum]; rw [Finset.sum_comm]
  have hcol_div : ∀ i, fieldDiv E (fun j => M j i) = D i M.det / M.det := by
    intro i
    rw [derivation_det_inverse (D i) M N hMN]
    unfold fieldDiv; simp_rw [chain, mixed]; rw [Finset.sum_comm]; field_simp
  rw [hsum]
  simp_rw [hsmul, column_directional D E M N hNM chain, hcol_div]
  unfold fieldDiv
  conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul]
  field_simp; ring
end ChainAndPiola

section CommonDenom
private def cleared {R σ τ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (B : MvPolynomial τ R) (G : σ → MvPolynomial τ R) (L : ℕ) :
    MvPolynomial τ R :=
  ∑ a ∈ p.support, C (coeff a p) * (∏ i ∈ a.support, G i ^ a i) * B ^ (L - a.sum (fun _ e => e))

private lemma cleared_homogeneous {R σ τ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (B : MvPolynomial τ R) (G : σ → MvPolynomial τ R) (L k : ℕ)
    (hp : p.totalDegree ≤ L) (hB : B.IsHomogeneous k) (hG : ∀ i, (G i).IsHomogeneous k) :
    (cleared p B G L).IsHomogeneous (k * L) := by
  apply IsHomogeneous.sum
  intro a ha
  have hdeg : a.sum (fun _ e => e) ≤ L := (le_totalDegree ha).trans hp
  have hprod : (∏ i ∈ a.support, G i ^ a i).IsHomogeneous (k * a.sum (fun _ e => e)) := by
    simpa only [Finsupp.sum, Finset.mul_sum] using
      IsHomogeneous.prod a.support (fun i => G i ^ a i) (fun i => k * a i)
        (fun i _ => (hG i).pow (a i))
  convert (hprod.C_mul (coeff a p)).mul (hB.pow (L - a.sum (fun _ e => e))) using 1
  rw [← Nat.mul_add, Nat.add_sub_of_le hdeg]

private lemma map_cleared {R σ τ S : Type*} [CommSemiring R] [CommSemiring S]
    (p : MvPolynomial σ R) (B : MvPolynomial τ R) (G : σ → MvPolynomial τ R) (L : ℕ)
    (hp : p.totalDegree ≤ L) (φ : MvPolynomial τ R →+* S) (b : S) (y : σ → S)
    (hB : φ B = b) (hG : ∀ i, φ (G i) = b * y i) :
    φ (cleared p B G L) = b ^ L * eval₂ (φ.comp C) y p := by
  rw [cleared, map_sum]
  change _ = b ^ L * (∑ a ∈ p.support, φ (C (coeff a p)) * (∏ i ∈ a.support, y i ^ a i))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg : a.sum (fun _ e => e) ≤ L := (le_totalDegree ha).trans hp
  simp only [map_mul, map_pow, map_prod, hB, hG, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpow : b ^ (∑ i ∈ a.support, a i) * b ^ (L - a.sum (fun _ e => e)) = b ^ L := by
    rw [← pow_add]; congr 1; exact Nat.add_sub_of_le hdeg
  calc
    _ = (b ^ (∑ i ∈ a.support, a i) * b ^ (L - a.sum (fun _ e => e))) *
        (φ (C (coeff a p)) * ∏ i ∈ a.support, y i ^ a i) := by ring
    _ = _ := by rw [hpow]

private lemma not_dvd_cleared {R σ τ S : Type*} [CommSemiring R] [CommSemiring S]
    (p : MvPolynomial σ R) (B : MvPolynomial τ R) (G : σ → MvPolynomial τ R) (L : ℕ)
    (hp : p.totalDegree ≤ L) (φ : MvPolynomial τ R →+* S) (b : S) (y : σ → S)
    (hB : φ B = b) (hG : ∀ i, φ (G i) = b * y i)
    (q : MvPolynomial τ R) (a : S) (ha : Prime a)
    (hq : a ∣ φ q) (hb : ¬ a ∣ b) (hpull : ¬ a ∣ eval₂ (φ.comp C) y p) :
    ¬ q ∣ cleared p B G L := by
  intro hdiv
  have hmap : a ∣ φ (cleared p B G L) := hq.trans (map_dvd φ hdiv)
  rw [map_cleared p B G L hp φ b y hB hG] at hmap
  exact ha.not_dvd_mul (fun hpow => hb (ha.dvd_of_dvd_pow hpow)) hpull hmap
end CommonDenom

section SixDimTransport
private def jacobian {K : Type*} [Field K] (a lam b c d v : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1 + v, 0, 0, 0, 0, a;
     1 - v, 0, 0, 0, 0, -a;
     b, 0, a, 0, 0, 0;
     c + lam * v, a * v, 0, a, 0, a * lam;
     c - lam * v, -a * v, 0, a, 0, -a * lam;
     d, 0, 0, 0, a, 0]

private def inverseJacobian {K : Type*} [Field K] (a lam b c d v : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1 / 2, 1 / 2, 0, 0, 0, 0;
     -lam / (2 * a * v), lam / (2 * a * v), 0, 1 / (2 * a * v), -1 / (2 * a * v), 0;
     -b / (2 * a), -b / (2 * a), 1 / a, 0, 0, 0;
     -c / (2 * a), -c / (2 * a), 0, 1 / (2 * a), 1 / (2 * a), 0;
     -d / (2 * a), -d / (2 * a), 0, 0, 0, 1 / a;
     (1 - v) / (2 * a), -(1 + v) / (2 * a), 0, 0, 0, 0]

private lemma jacobian_det {K : Type*} [Field K] [CharZero K] (a lam b c d v : K) :
    (jacobian a lam b c d v).det = 4 * a ^ 5 * v := by
  simp [jacobian, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix]
  dsimp [Fin.succAbove, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  ring

private lemma jacobian_mul_inverse {K : Type*} [Field K] [CharZero K]
    (a lam b c d v : K) (ha : a ≠ 0) (hv : v ≠ 0) :
    jacobian a lam b c d v * inverseJacobian a lam b c d v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    field_simp <;> ring

private lemma inverse_mul_jacobian {K : Type*} [Field K] [CharZero K]
    (a lam b c d v : K) (ha : a ≠ 0) (hv : v ≠ 0) :
    inverseJacobian a lam b c d v * jacobian a lam b c d v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    field_simp <;> ring

private def physicalDerivative {K : Type*} [Field K]
    (D : Fin 6 → Derivation ℤ K K) (a lam b c d v : K) (j : Fin 6) : Derivation ℤ K K :=
  ∑ k, inverseJacobian a lam b c d v k j • D k

private lemma physicalDerivative_apply {K : Type*} [Field K]
    (D : Fin 6 → Derivation ℤ K K) (a lam b c d v : K) (j : Fin 6) (z : K) :
    physicalDerivative D a lam b c d v j z = ∑ k, inverseJacobian a lam b c d v k j * D k z := by
  change Derivation.coeFnAddMonoidHom (∑ k, inverseJacobian a lam b c d v k j • D k) z = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]

private def chartCoordinates {K : Type*} [Field K] (x : Fin 6 → K) : Fin 6 → K :=
  ![x 0 * (1 + x 5), x 0 * (1 - x 5), x 0 * x 2,
    x 0 * (x 3 + x 1 * x 5), x 0 * (x 3 - x 1 * x 5), x 0 * x 4]

private lemma chartCoordinates_derivative {K : Type*} [Field K] [CharZero K]
    (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0) (i j : Fin 6) :
    D i (chartCoordinates x j) = jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j i := by
  fin_cases i <;> fin_cases j <;>
    simp [chartCoordinates, jacobian, Derivation.leibniz, smul_eq_mul, hx] <;> ring

private lemma physicalDerivative_coordinate {K : Type*} [Field K] [CharZero K]
    (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0) (i j : Fin 6) :
    physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i (chartCoordinates x j) =
      if j = i then 1 else 0 := by
  rw [physicalDerivative_apply]
  simp_rw [chartCoordinates_derivative D x hx]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M j i)
    (jacobian_mul_inverse (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ha hv)
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h

private def volumeCurrent {K : Type*} [Field K] (a : K) (w : Fin 5 → K) : Fin 6 → K :=
  Fin.cases 0 (fun i => a ^ 5 * w i)

private def physicalCurrent {K : Type*} [Field K] (a lam v : K) (w : Fin 5 → K) : Fin 6 → K :=
  ![a * w 4 / (4 * v), -a * w 4 / (4 * v), a * w 1 / (4 * v),
    a * (v * w 0 + w 2 + lam * w 4) / (4 * v),
    a * (-v * w 0 + w 2 - lam * w 4) / (4 * v), a * w 3 / (4 * v)]

private lemma normalized_current_transport {K : Type*} [Field K] [CharZero K]
    (D : Fin 6 → Derivation ℤ K K) (x : Fin 6 → K)
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (ha : x 0 ≠ 0) (hv : x 5 ≠ 0)
    (H AH r : K) (w : Fin 5 → K)
    (hnormal : (∑ i : Fin 5, w i * D i.succ H) = AH)
    (hdiv : (∑ i : Fin 5, D i.succ (w i)) = H * r) :
    let E := physicalDerivative D (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    let V := physicalCurrent (x 0) (x 1) (x 5) w
    (∑ j, V j * E j ((x 0) ^ 6 * H)) = (x 0) ^ 6 * AH / (4 * x 5) ∧
      fieldDiv E V = ((x 0) ^ 6 * H) * (r / (4 * (x 0) ^ 6 * x 5)) := by
  dsimp only
  have hradial : ∀ i : Fin 5, D i.succ (x 0) = 0 := fun i => by simp [hx]
  have hdet : (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det ≠ 0 := by
    rw [jacobian_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hv
  have hpiola_cur : physicalCurrent (x 0) (x 1) (x 5) w = fun j =>
      ∑ i, (volumeCurrent (x 0) w i / (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det) *
        jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j i := by
    rw [jacobian_det]
    funext j; fin_cases j <;>
      simp [physicalCurrent, volumeCurrent, jacobian, Fin.sum_univ_succ] <;>
      field_simp <;> ring
  have hmixed : ∀ i j k, D k (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j i) =
      D i (jacobian (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) j k) := by
    intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [jacobian, Derivation.leibniz, smul_eq_mul, hx]
  have hvol_con : (∑ i, volumeCurrent (x 0) w i * D i ((x 0) ^ 6 * H)) =
      (x 0) ^ 11 * ∑ i : Fin 5, w i * D i.succ H := by
    rw [Fin.sum_univ_succ]
    simp only [volumeCurrent, Fin.cases_zero, zero_mul, Fin.cases_succ,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, hradial,
      mul_zero, zero_mul, add_zero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have hvol_div : fieldDiv D (volumeCurrent (x 0) w) =
      (x 0) ^ 5 * ∑ i : Fin 5, D i.succ (w i) := by
    rw [fieldDiv, Fin.sum_univ_succ]
    simp [volumeCurrent, Derivation.leibniz, Derivation.leibniz_pow, hradial, smul_eq_mul, Finset.mul_sum]
  rw [hpiola_cur]
  constructor
  · rw [piola_contraction D _ _ _ (inverse_mul_jacobian _ _ _ _ _ _ ha hv)
      (physicalDerivative_apply D _ _ _ _ _ _), hvol_con, hnormal, jacobian_det]
    field_simp <;> ring
  · rw [piola_divergence D _ _ _ (jacobian_mul_inverse _ _ _ _ _ _ ha hv)
      (inverse_mul_jacobian _ _ _ _ _ _ ha hv) hdet (physicalDerivative_apply D _ _ _ _ _ _) hmixed,
      hvol_div, hdiv, jacobian_det]
    field_simp <;> ring

private def K6 := FractionRing (AmbientPoly 5)
private instance : Field K6 := inferInstanceAs (Field (FractionRing (AmbientPoly 5)))
private instance : Algebra (AmbientPoly 5) K6 := inferInstanceAs (Algebra (AmbientPoly 5) (FractionRing (AmbientPoly 5)))
private instance : IsFractionRing (AmbientPoly 5) K6 := inferInstanceAs (IsFractionRing (AmbientPoly 5) (FractionRing (AmbientPoly 5)))
private instance : Algebra ℚ K6 := inferInstanceAs (Algebra ℚ (FractionRing (AmbientPoly 5)))
private instance : IsScalarTower ℚ (AmbientPoly 5) K6 := inferInstanceAs (IsScalarTower ℚ (AmbientPoly 5) (FractionRing (AmbientPoly 5)))
private instance : CharZero K6 :=
  ⟨fun a b h =>
    Nat.cast_injective ((algebraMap ℚ K6).injective (by simpa only [map_natCast] using h))⟩

private def embed6 : AmbientPoly 5 →+* K6 := algebraMap (AmbientPoly 5) K6
private def coeffMap6 : ℂ →+* K6 := embed6.comp C
private def x6 (i : Fin 6) : K6 := embed6 (X i)
private def delta6 (i : Fin 6) : Derivation ℤ K6 K6 :=
  (extendFrac (P := AmbientPoly 5) (F := K6) ((pderiv i).restrictScalars ℚ)).restrictScalars ℤ

private lemma embed6_injective : Function.Injective embed6 := IsFractionRing.injective _ _

@[simp] private lemma delta6_embed (i : Fin 6) (p : AmbientPoly 5) :
    delta6 i (embed6 p) = embed6 (pderiv i p) :=
  extendFrac_map (F := K6) ((pderiv i : Derivation ℂ (AmbientPoly 5) (AmbientPoly 5)).restrictScalars ℚ) p

@[simp] private lemma delta6_coeff (i : Fin 6) (c : ℂ) : delta6 i (coeffMap6 c) = 0 := by
  simp [coeffMap6]

private lemma delta6_coord (i j : Fin 6) : delta6 i (x6 j) = if i = j then 1 else 0 := by
  simp [x6, pderiv_X, Pi.single_apply, eq_comm]

private lemma coord6_ne_zero (i : Fin 6) : x6 i ≠ 0 := by
  intro h
  exact (X_ne_zero i) (embed6_injective (by simpa [x6] using h))

private def affineMap6 : ChartPoly →+* K6 := embed6.comp (rename Fin.succ).toRingHom

private lemma affineMap6_as_eval :
    affineMap6 = eval₂Hom coeffMap6 (fun i : Fin 5 => x6 i.succ) := by
  ext i <;> simp [affineMap6, coeffMap6, x6]

private lemma affineMap6_injective : Function.Injective affineMap6 := by
  rw [affineMap6_as_eval]
  apply injective_of_coordinate_derivations coeffMap6 (fun i : Fin 5 => x6 i.succ) (fun i => delta6 i.succ)
  · exact fun i c => delta6_coeff i.succ c
  · intro i j; simp [delta6_coord, eq_comm]

@[simp] private lemma delta6_affineMap (i : Fin 5) (p : ChartPoly) :
    delta6 i.succ (affineMap6 p) = affineMap6 (pderiv i p) := by
  change delta6 i.succ (embed6 (rename Fin.succ p)) = embed6 (rename Fin.succ (pderiv i p))
  rw [delta6_embed]
  have hp : pderiv i.succ (rename Fin.succ p) = rename Fin.succ (pderiv i p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp =>
      simp only [map_mul, rename_X, Derivation.leibniz, hp, pderiv_X, smul_eq_mul,
        Pi.single_apply, (Fin.succ_injective 5).eq_iff]
      split_ifs <;> simp
  rw [hp]

private def physicalMap6 : AmbientPoly 5 →+* K6 := eval₂Hom coeffMap6 (chartCoordinates x6)
private def theta6 : Fin 6 → Derivation ℤ K6 K6 :=
  physicalDerivative delta6 (x6 0) (x6 1) (x6 2) (x6 3) (x6 4) (x6 5)

private lemma physicalMap6_injective : Function.Injective physicalMap6 :=
  injective_of_coordinate_derivations coeffMap6 (chartCoordinates x6) theta6
    (fun i c => by simp only [theta6, physicalDerivative_apply, delta6_coeff, mul_zero, Finset.sum_const_zero])
    (physicalDerivative_coordinate delta6 x6 delta6_coord (coord6_ne_zero 0) (coord6_ne_zero 5))

@[simp] private lemma theta6_physicalMap (i : Fin 6) (p : AmbientPoly 5) :
    theta6 i (physicalMap6 p) = physicalMap6 (pderiv i p) := by
  have hc : ∀ c, theta6 i (coeffMap6 c) = 0 := fun c => by
    simp only [theta6, physicalDerivative_apply, delta6_coeff, mul_zero, Finset.sum_const_zero]
  rw [physicalMap6, derivation_eval₂_chain (theta6 i) coeffMap6 (chartCoordinates x6) hc p]
  simp [theta6, physicalDerivative_coordinate delta6 x6 delta6_coord (coord6_ne_zero 0) (coord6_ne_zero 5)]

/-- Universal homogeneous scaling identity on the reflection chart: for any homogeneous
degree-6 polynomial `P`, `physicalMap6 P = (x6 0)^6 * affineMap6 (affinePullback P)`. -/
private lemma physicalMap6_of_isHomogeneous6 (P : AmbientPoly 5) (hP : P.IsHomogeneous 6) :
    physicalMap6 P = (x6 0) ^ 6 * affineMap6 (affinePullback P) := by
  have hcoord : ∀ j : Fin 6, chartCoordinates x6 j = x6 0 * affineMap6 (affinePullback (X j)) := by
    intro j
    fin_cases j <;>
      simp [chartCoordinates, affinePullback, affineMap6_as_eval, eval₂Hom_X', coeffMap6, x6, map_add, map_sub, map_mul] <;>
      ring
  have hcomp : affineMap6.comp affinePullback =
      eval₂Hom coeffMap6 (fun j : Fin 6 => affineMap6 (affinePullback (X j))) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [affineMap6, affinePullback, coeffMap6]
    · intro j; simp
  change eval₂Hom coeffMap6 (chartCoordinates x6) P = (x6 0) ^ 6 * (affineMap6.comp affinePullback) P
  rw [hcomp, ← P.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hdeg : ∑ j ∈ m.support, m j = 6 := (hP.degree_eq_sum_deg_support hm).symm
  simp only [eval₂Hom_monomial, Finsupp.prod]
  simp_rw [hcoord, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private def U6 : AmbientPoly 5 := X 0 + X 1
private def S6 : AmbientPoly 5 := X 0 - X 1
private def T6 : AmbientPoly 5 := X 3 - X 4
private def B6 : AmbientPoly 5 := U6 * S6
private def G6 : Fin 5 → AmbientPoly 5 :=
  ![U6 * T6, 2 * X 2 * S6, (X 3 + X 4) * S6, 2 * X 5 * S6, S6 ^ 2]

private lemma U6_hom : U6.IsHomogeneous 1 := (isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)
private lemma S6_hom : S6.IsHomogeneous 1 := (isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 1)
private lemma T6_hom : T6.IsHomogeneous 1 := (isHomogeneous_X ℂ 3).sub (isHomogeneous_X ℂ 4)
private lemma B6_hom : B6.IsHomogeneous 2 := U6_hom.mul S6_hom
private lemma G6_hom (i : Fin 5) : (G6 i).IsHomogeneous 2 := by
  fin_cases i
  · exact U6_hom.mul T6_hom
  · simpa [G6, map_ofNat] using ((isHomogeneous_X ℂ 2).C_mul 2).mul S6_hom
  · exact ((isHomogeneous_X ℂ 3).add (isHomogeneous_X ℂ 4)).mul S6_hom
  · simpa [G6, map_ofNat] using ((isHomogeneous_X ℂ 5).C_mul 2).mul S6_hom
  · exact S6_hom.pow 2

private def liftPoly (p : ChartPoly) (L : ℕ) : AmbientPoly 5 := cleared p B6 G6 L

private lemma liftPoly_hom (p : ChartPoly) (L : ℕ) (hp : p.totalDegree ≤ L) :
    (liftPoly p L).IsHomogeneous (2 * L) :=
  cleared_homogeneous p B6 G6 L 2 hp B6_hom G6_hom

private lemma affinePullback_B6 : affinePullback B6 = 4 * X 4 := by
  simp [affinePullback, B6, U6, S6]; ring

private lemma affinePullback_G6 (i : Fin 5) : affinePullback (G6 i) = (4 * X 4) * X i := by
  fin_cases i <;> simp [affinePullback, G6, U6, S6, T6, map_ofNat] <;> ring

private def certDenom (p : ChartPoly) (L : ℕ) : AmbientPoly 5 := 8 * S6 ^ 2 * liftPoly p L

private def certNum (N : Fin 5 → ChartPoly) (L : ℕ) : Fin 6 → AmbientPoly 5 :=
  ![U6 ^ 2 * S6 * liftPoly (N 4) L,
    -(U6 ^ 2 * S6 * liftPoly (N 4) L),
    U6 ^ 2 * S6 * liftPoly (N 1) L,
    U6 * S6 ^ 2 * liftPoly (N 0) L + U6 ^ 2 * S6 * liftPoly (N 2) L + U6 ^ 2 * T6 * liftPoly (N 4) L,
    -(U6 * S6 ^ 2 * liftPoly (N 0) L) + U6 ^ 2 * S6 * liftPoly (N 2) L - U6 ^ 2 * T6 * liftPoly (N 4) L,
    U6 ^ 2 * S6 * liftPoly (N 3) L]

private def certQuot (Q : ChartPoly) (L : ℕ) : AmbientPoly 5 :=
  1024 * U6 ^ (L - 5) * S6 ^ (L + 3) * liftPoly Q L

private lemma physicalMap6_U6 : physicalMap6 U6 = 2 * x6 0 := by
  simp [physicalMap6, U6, chartCoordinates]; ring
private lemma physicalMap6_S6 : physicalMap6 S6 = 2 * x6 0 * x6 5 := by
  simp [physicalMap6, S6, chartCoordinates]; ring
private lemma physicalMap6_T6 : physicalMap6 T6 = 2 * x6 0 * x6 1 * x6 5 := by
  simp [physicalMap6, T6, chartCoordinates]; ring
private lemma physicalMap6_B6 : physicalMap6 B6 = 4 * (x6 0) ^ 2 * x6 5 := by
  simp [B6, physicalMap6_U6, physicalMap6_S6]; ring
private lemma physicalMap6_G6 (i : Fin 5) :
    physicalMap6 (G6 i) = (4 * (x6 0) ^ 2 * x6 5) * x6 i.succ := by
  fin_cases i <;> simp [physicalMap6, G6, U6, S6, T6, chartCoordinates, map_ofNat] <;> ring

private lemma physicalMap6_liftPoly (p : ChartPoly) (L : ℕ) (hp : p.totalDegree ≤ L) :
    physicalMap6 (liftPoly p L) = (4 * (x6 0) ^ 2 * x6 5) ^ L * affineMap6 p := by
  have hc : physicalMap6.comp (C : ℂ →+* AmbientPoly 5) = coeffMap6 := by ext c; simp [physicalMap6]
  have h := map_cleared p B6 G6 L hp physicalMap6 (4 * (x6 0) ^ 2 * x6 5) (fun i : Fin 5 => x6 i.succ)
    physicalMap6_B6 physicalMap6_G6
  simpa only [liftPoly, hc, affineMap6_as_eval, coe_eval₂Hom] using h

private lemma hom_of_isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℕ}
    (h : P.IsHomogeneous k) : Homogeneous P (k : ℤ) := by
  intro m hm
  exact_mod_cast (show m.degree = k by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm)

private lemma quot_contraction {σ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℂ →+* K6) (E : σ → Derivation ℤ K6 K6)
    (compat : ∀ i p, E i (φ p) = φ (pderiv i p))
    (D F : MvPolynomial σ ℂ) (N : σ → MvPolynomial σ ℂ) :
    (∑ i, (φ (N i) / φ D) * E i (φ F)) = φ (dirPoly F N) / φ D := by
  simp only [compat, dirPoly, map_sum, map_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; ring

private lemma quot_divergence {σ : Type*} [Fintype σ]
    (φ : MvPolynomial σ ℂ →+* K6) (E : σ → Derivation ℤ K6 K6)
    (compat : ∀ i p, E i (φ p) = φ (pderiv i p))
    (D : MvPolynomial σ ℂ) (N : σ → MvPolynomial σ ℂ) :
    fieldDiv E (fun i => φ (N i) / φ D) = φ (divNumPoly D N) / (φ D) ^ 2 := by
  simp only [fieldDiv, Derivation.leibniz_div, compat, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hs : (∑ i, (φ D * φ (pderiv i (N i)) - φ (N i) * φ (pderiv i D))) =
      φ (divNumPoly D N) := by
    simp only [divNumPoly, dirPoly, map_sub, map_mul, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [hs]; simp only [div_eq_mul_inv, inv_pow]; ring

end SixDimTransport

end ReflectionChartTransport

theorem solution
    (F A : HodgeComputer.AmbientPoly 5) (f P : HodgeComputer.ReflectionChart.ChartPoly)
    (hF_hom : F.IsHomogeneous 6) (hA_hom : A.IsHomogeneous 6)
    (hF_irred : Irreducible F) (hH_irred : Irreducible (HodgeComputer.ReflectionChart.squareLift f))
    (hF_pull : HodgeComputer.ReflectionChart.affinePullback F = HodgeComputer.ReflectionChart.squareLift f)
    (hA_pull : HodgeComputer.ReflectionChart.affinePullback A = HodgeComputer.ReflectionChart.squareLift P)
    (h_pt_zero : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift f) = 0)
    (h_pt_fu : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift (MvPolynomial.pderiv 4 f)) ≠ 0)
    (h_prim : HodgeComputer.ReflectionChart.RelativePrimitive f P) :
    HodgeComputer.HasCertificate F A 6 1 := by
  open ReflectionChartTransport MvPolynomial HodgeComputer HodgeComputer.ReflectionChart in
  obtain ⟨D_aff, Q_aff, N, hDaff_ne, hDaff_legal, hnormal, hdiv⟩ :=
    affine_normalized_of_relative_primitive f P hH_irred h_pt_zero h_pt_fu h_prim
  let L := max 5 (max D_aff.totalDegree (max Q_aff.totalDegree
    (Finset.univ.sup (fun i => (N i).totalDegree))))
  have hL : 5 ≤ L := Nat.le_max_left _ _
  have hLD : D_aff.totalDegree ≤ L := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hLQ : Q_aff.totalDegree ≤ L :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hLN : ∀ i, (N i).totalDegree ≤ L := by
    intro i
    have hi : (N i).totalDegree ≤ Finset.univ.sup (fun j => (N j).totalDegree) :=
      Finset.le_sup (f := fun j => (N j).totalDegree) (Finset.mem_univ i)
    dsimp [L]; omega
  -- Legality of `certDenom D_aff L`
  have hF_prime : Prime F := irreducible_iff_prime.mp hF_irred
  have hH_prime : Prime (squareLift f) := irreducible_iff_prime.mp hH_irred
  have hnot_H_dvd_4v : ¬ squareLift f ∣ (4 * X 4 : ChartPoly) := by
    intro hdiv4
    have hmap := map_dvd (eval normalPoint) hdiv4
    rw [h_pt_zero, zero_dvd_iff] at hmap
    have hz : (4 : ℂ) * Complex.I = 0 := by simpa [normalPoint] using hmap
    exact (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) Complex.I_ne_zero) hz
  have hnot_F_dvd_lift : ¬ F ∣ liftPoly D_aff L := by
    apply not_dvd_cleared D_aff B6 G6 L hLD affinePullback (4 * X 4) X
      affinePullback_B6 affinePullback_G6 F (squareLift f) hH_prime
    · rw [hF_pull]
    · exact hnot_H_dvd_4v
    · have hc : affinePullback.comp (C : ℂ →+* AmbientPoly 5) = (C : ℂ →+* ChartPoly) := by
        ext r; simp [affinePullback]
      rw [hc, eval₂_eta]
      exact hH_irred.isRelPrime_iff_not_dvd.mp hDaff_legal
  have hnot_F_dvd_pt : ∀ p : AmbientPoly 5, eval normalPoint (affinePullback p) ≠ 0 → ¬ F ∣ p := by
    intro p hp hdivp
    have hmap := map_dvd ((eval normalPoint).comp affinePullback) hdivp
    simp only [RingHom.comp_apply, hF_pull, h_pt_zero, zero_dvd_iff] at hmap
    exact hp hmap
  have hnot_F_dvd_S6 : ¬ F ∣ S6 := by
    apply hnot_F_dvd_pt
    simp [affinePullback, S6, normalPoint, Complex.I_ne_zero]
  have hnot_F_dvd_8 : ¬ F ∣ (8 : AmbientPoly 5) := by
    apply hnot_F_dvd_pt
    norm_num [affinePullback, map_ofNat]
  have hnot_F_dvd_den : ¬ F ∣ certDenom D_aff L := by
    apply hF_prime.not_dvd_mul
    · exact hF_prime.not_dvd_mul hnot_F_dvd_8 (fun h => hnot_F_dvd_S6 (hF_prime.dvd_of_dvd_pow h))
    · exact hnot_F_dvd_lift
  have hden_ne : certDenom D_aff L ≠ 0 := fun hz => hnot_F_dvd_den (hz ▸ dvd_zero _)
  have hden_legal : IsRelPrime F (certDenom D_aff L) :=
    hF_irred.isRelPrime_iff_not_dvd.mpr hnot_F_dvd_den
  have hden_hom : (certDenom D_aff L).IsHomogeneous (2 * L + 2) := by
    have h := ((S6_hom.pow 2).C_mul (8 : ℂ)).mul (liftPoly_hom D_aff L hLD)
    simpa only [map_ofNat, Nat.mul_one, Nat.one_mul, Nat.add_comm, certDenom] using h
  have hnum_hom : ∀ i : Fin 6, (certNum N L i).IsHomogeneous (2 * L + 3) := by
    intro i
    have hstd (j : Fin 5) : (U6 ^ 2 * S6 * liftPoly (N j) L).IsHomogeneous (2 * L + 3) := by
      simpa [Nat.add_comm] using (((U6_hom.pow 2).mul S6_hom).mul (liftPoly_hom (N j) L (hLN j)))
    have hlam : (U6 * S6 ^ 2 * liftPoly (N 0) L).IsHomogeneous (2 * L + 3) := by
      simpa [Nat.add_comm] using ((U6_hom.mul (S6_hom.pow 2)).mul (liftPoly_hom (N 0) L (hLN 0)))
    have hlast : (U6 ^ 2 * T6 * liftPoly (N 4) L).IsHomogeneous (2 * L + 3) := by
      simpa [Nat.add_comm] using (((U6_hom.pow 2).mul T6_hom).mul (liftPoly_hom (N 4) L (hLN 4)))
    fin_cases i
    · exact hstd 4
    · exact (hstd 4).neg
    · exact hstd 1
    · exact (hlam.add (hstd 2)).add hlast
    · exact (hlam.neg.add (hstd 2)).sub hlast
    · exact hstd 3
  -- Transport equations via `K6`
  have hd_aff_map : affineMap6 D_aff ≠ 0 := fun h => hDaff_ne (affineMap6_injective (by simpa using h))
  have hn_aff : (∑ i : Fin 5, (affineMap6 (N i) / affineMap6 D_aff) * delta6 i.succ (affineMap6 (squareLift f))) =
      affineMap6 (reflectedSource P) := by
    rw [quot_contraction affineMap6 (fun i : Fin 5 => delta6 i.succ) delta6_affineMap, hnormal, map_mul]
    field_simp
  have hd_aff : (∑ i : Fin 5, delta6 i.succ (affineMap6 (N i) / affineMap6 D_aff)) =
      affineMap6 (squareLift f) * (affineMap6 Q_aff / (affineMap6 D_aff) ^ 2) := by
    change fieldDiv (fun i : Fin 5 => delta6 i.succ) _ = _
    rw [quot_divergence affineMap6 (fun i : Fin 5 => delta6 i.succ) delta6_affineMap, hdiv, map_mul]
    ring
  have hp := normalized_current_transport delta6 x6 delta6_coord
    (coord6_ne_zero 0) (coord6_ne_zero 5)
    (affineMap6 (squareLift f)) (affineMap6 (reflectedSource P))
    (affineMap6 Q_aff / (affineMap6 D_aff) ^ 2)
    (fun i => affineMap6 (N i) / affineMap6 D_aff) hn_aff hd_aff
  change
    (∑ j, physicalCurrent (x6 0) (x6 1) (x6 5) (fun i => affineMap6 (N i) / affineMap6 D_aff) j *
      theta6 j ((x6 0) ^ 6 * affineMap6 (squareLift f))) = _ ∧
    fieldDiv theta6 (physicalCurrent (x6 0) (x6 1) (x6 5)
      (fun i => affineMap6 (N i) / affineMap6 D_aff)) = _ at hp
  have hmap_F : physicalMap6 F = (x6 0) ^ 6 * affineMap6 (squareLift f) := by
    rw [physicalMap6_of_isHomogeneous6 F hF_hom, hF_pull]
  have hmap_A : 4 * x6 5 * physicalMap6 A = (x6 0) ^ 6 * affineMap6 (reflectedSource P) := by
    rw [physicalMap6_of_isHomogeneous6 A hA_hom, hA_pull, reflectedSource]
    have hx5 : affineMap6 (X 4) = x6 5 := by simp [affineMap6, x6]
    have hc4 : affineMap6 (C 4) = 4 := by simp [affineMap6, embed6, map_ofNat]
    simp only [map_mul, hc4, hx5]; ring
  have hcur_map : (fun i => physicalMap6 (certNum N L i) / physicalMap6 (certDenom D_aff L)) =
      physicalCurrent (x6 0) (x6 1) (x6 5) (fun i => affineMap6 (N i) / affineMap6 D_aff) := by
    have ha := coord6_ne_zero 0
    have hv := coord6_ne_zero 5
    have hb : 4 * (x6 0) ^ 2 * x6 5 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) hv
    funext i; fin_cases i <;>
      simp [certNum, certDenom, physicalCurrent, map_ofNat,
        physicalMap6_U6, physicalMap6_S6, physicalMap6_T6,
        physicalMap6_liftPoly D_aff L hLD,
        physicalMap6_liftPoly (N 0) L (hLN 0),
        physicalMap6_liftPoly (N 1) L (hLN 1),
        physicalMap6_liftPoly (N 2) L (hLN 2),
        physicalMap6_liftPoly (N 3) L (hLN 3),
        physicalMap6_liftPoly (N 4) L (hLN 4)] <;>
      field_simp <;> ring
  have hquot_map : physicalMap6 (certQuot Q_aff L) =
      (physicalMap6 (certDenom D_aff L)) ^ 2 *
        (affineMap6 Q_aff / (4 * (x6 0) ^ 6 * x6 5 * (affineMap6 D_aff) ^ 2)) := by
    have ha := coord6_ne_zero 0
    have hv := coord6_ne_zero 5
    have hu : physicalMap6 U6 ≠ 0 := by rw [physicalMap6_U6]; exact mul_ne_zero (by norm_num) ha
    apply mul_left_cancel₀ (pow_ne_zero 5 hu)
    have hclear : U6 ^ 5 * certQuot Q_aff L = 1024 * B6 ^ L * S6 ^ 3 * liftPoly Q_aff L := by
      have hpow : U6 ^ 5 * U6 ^ (L - 5) = U6 ^ L := by rw [← pow_add, Nat.add_sub_of_le hL]
      simp only [certQuot, B6, mul_pow]
      calc
        _ = 1024 * (U6 ^ 5 * U6 ^ (L - 5)) * S6 ^ L * S6 ^ 3 * liftPoly Q_aff L := by
          simp only [pow_add]; ring
        _ = _ := by rw [hpow]; ring
    have hc := congrArg physicalMap6 hclear
    simp only [map_mul, map_pow, map_ofNat] at hc
    rw [hc]
    simp only [certDenom, map_mul, map_pow, map_ofNat,
      physicalMap6_U6, physicalMap6_S6, physicalMap6_B6,
      physicalMap6_liftPoly D_aff L hLD, physicalMap6_liftPoly Q_aff L hLQ]
    field_simp <;> ring
  rw [← hmap_F, ← hcur_map] at hp
  have hden_map : physicalMap6 (certDenom D_aff L) ≠ 0 := fun h =>
    hden_ne (physicalMap6_injective (by simpa using h))
  have hs : (x6 0) ^ 6 * affineMap6 (reflectedSource P) / (4 * x6 5) = physicalMap6 A := by
    rw [← hmap_A]; field_simp [coord6_ne_zero 5]
  have heq1 : directional F (certNum N L) = A * certDenom D_aff L := by
    apply physicalMap6_injective
    rw [map_mul]
    have h := hp.1
    rw [hs, quot_contraction physicalMap6 theta6 theta6_physicalMap] at h
    exact (div_eq_iff hden_map).mp h
  have heq2 : divergenceNumerator (certDenom D_aff L) (certNum N L) = F * certQuot Q_aff L := by
    apply physicalMap6_injective
    rw [map_mul]
    have h := hp.2
    rw [quot_divergence physicalMap6 theta6 theta6_physicalMap] at h
    have h' := (div_eq_iff (pow_ne_zero 2 hden_map)).mp h
    rw [hquot_map]
    change physicalMap6 (divNumPoly (certDenom D_aff L) (certNum N L)) = _
    calc
      _ = (physicalMap6 F * ((affineMap6 Q_aff / (affineMap6 D_aff) ^ 2) /
          (4 * (x6 0) ^ 6 * x6 5))) * (physicalMap6 (certDenom D_aff L)) ^ 2 := h'
      _ = _ := by ring
  refine ⟨certDenom D_aff L, certNum N L, certQuot Q_aff L, ?_⟩
  refine ⟨hF_irred.ne_zero, hF_hom, ?_, hden_ne, ?_, ?_, hden_legal, ?_⟩
  · intro m hm
    exact (hom_of_isHomogeneous hA_hom hm).trans (by norm_num)
  · rw [hden_hom.totalDegree hden_ne]; exact hden_hom
  · intro i
    rw [hden_hom.totalDegree hden_ne]
    convert hom_of_isHomogeneous (hnum_hom i) using 1
    push_cast; omega
  · unfold defect
    rw [Nat.cast_one, one_mul, pow_two, heq1, heq2]
    ring
