-- Prove2me | solution 1 for MasulloRH.cell_operator_product_and_winding_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:25:32.537266+00:00
-- url     : https://prove2.me/submissions/02d0dc8f-d91e-4d0f-913d-5165393bffa9

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ComplexConjugate

private theorem circle_product_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b q : ℂ) (hab : a*b=q) (P : H →L[ℂ] H) (F : ℕ → H →L[ℂ] H) :
    let E := fun m n : ℕ => ((1-q)*a^m*b^n) • (1-P) -
      (if m=0 ∧ n=0 then 1 else 0)
    let K := fun i j : ℕ => ∑ m ∈ Finset.range (i+1), F (i-m) * E m j
    let C := fun i j : ℕ => ∑ m ∈ Finset.range (i+1),
      ((1-q)*a^m*b^j) • (F (i-m)*(1-P))
    (∀ i j, K i j = C i j - (if j=0 then F i else 0)) ∧
    ∀ n, C (n+1) (n+1) =
      q • C n n + ((1-q)*b^(n+1)) • (F (n+1)*(1-P)) := by
  dsimp only
  constructor
  · intro i j
    by_cases hj : j = 0
    · subst j
      simp only [mul_sub, mul_smul_comm, Finset.sum_sub_distrib, and_true,
        pow_zero, mul_one]
      congr 1
      rw [Finset.sum_eq_single 0]
      · simp
      · intro m hm hne; simp [hne]
      · simp
    · simp [hj]
  · intro n
    rw [Finset.sum_range_succ', Finset.smul_sum]
    simp only [pow_zero, mul_one, Nat.sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.succ_sub_succ_eq_sub, smul_smul]
    congr 1
    rw [pow_succ, pow_succ, ← hab]
    ring

private theorem circle_idempotent_column {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b q : ℂ) (P : H →L[ℂ] H) (hPP : P*P=P) (F : ℕ → H →L[ℂ] H) (i : ℕ) :
    (∑ m ∈ Finset.range (i+1), ((1-q)*a^m*b^0) • (F (i-m)*(1-P))) * P = 0 := by
  have h : (1-P)*P=0 := by rw [sub_mul, one_mul, hPP, sub_self]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc, mul_assoc, h, mul_zero, smul_zero, Finset.sum_const_zero]

private theorem cell_circle_phases (r : ℝ) (hr : 0 < r) (hr' : r < 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    let a := (r : ℂ) * (starRingEnd ℂ) u
    let b := (r : ℂ) * u
    a*b = ((r^2 : ℝ) : ℂ) ∧ (∀ j : ℕ, b^j ≠ 0) ∧
      HasSum (fun k : ℕ => (1-r^2) * ‖a‖^(2*k)) 1 := by
  dsimp only
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hn : ‖(r : ℂ) * (starRingEnd ℂ) u‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu]
  refine ⟨?_, fun j => pow_ne_zero j (mul_ne_zero (by exact_mod_cast hr.ne') hu0), ?_⟩
  · rw [mul_mul_mul_comm, Complex.conj_mul', hu]
    simp [sq]
  · have hq : r^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hr') (show 0 < 1+r by linarith)]
    have h := (hasSum_geometric_of_lt_one (sq_nonneg r) hq).mul_left (1-r^2)
    have he : 1 - r^2 ≠ 0 := (sub_pos.mpr hq).ne'
    simpa only [hn, pow_mul, mul_inv_cancel₀ he] using h

private theorem cell_circle_inverse {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : H →L[ℂ] H) (hP : P * P = P) (q : ℂ) (hq : q ≠ 0) :
    let N : H →L[ℂ] H := q • 1 + (1 - q) • P
    let S : H →L[ℂ] H := q⁻¹ • (1 - P) + P
    N * S = 1 ∧ S * N = 1 ∧ (1 - P) * P = 0 := by
  let Q := (1 : H →L[ℂ] H) - P
  have hQP : Q * P = 0 := by simp [Q, sub_mul, hP]
  have hPQ : P * Q = 0 := by simp [Q, mul_sub, hP]
  have hQQ : Q * Q = Q := by dsimp only [Q]; rw [mul_sub, mul_one, hQP, sub_zero]
  have hN : q • (1 : H →L[ℂ] H) + (1 - q) • P = q • Q + P := by
    dsimp only [Q]
    rw [smul_sub, sub_smul, one_smul]
    abel
  dsimp only
  change _ * (q⁻¹ • Q + P) = 1 ∧ (q⁻¹ • Q + P) * _ = 1 ∧ Q * P = 0
  rw [hN]
  refine ⟨?_, ?_, hQP⟩ <;>
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hQQ, hQP, hPQ, hP, mul_inv_cancel₀ hq, inv_mul_cancel₀ hq,
      zero_add, add_zero, smul_zero, one_smul] <;>
    exact sub_add_cancel _ _

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (F : ℕ → H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (hr' : r < 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    let a := (r:ℂ) * (starRingEnd ℂ) u
    let b := (r:ℂ) * u
    let q := ((r^2 : ℝ) : ℂ)
    let train := fun m : ℕ => ((Real.sqrt (1-r^2):ℝ):ℂ)*a^m
    let P := W.starProjection
    let E := fun m n : ℕ => ((1-q)*a^m*b^n) • (1-P) -
      (if m=0 ∧ n=0 then 1 else 0)
    let K := fun i j : ℕ => ∑ m ∈ Finset.range (i+1), F (i-m) * E m j
    let T := fun j => K j j
    let N : H →L[ℂ] H := q • 1 + (1-q) • P
    let S : H →L[ℂ] H := q⁻¹ • (1-P) + P
    let Z := -(T 0 * S)
    let G := fun n : ℕ => (1-q)⁻¹ •
      (T (n+1) - q • T n - (if n=0 then q • Z else 0)) -
      b^(n+1) • (K (n+1) 0 * P)
    (∀ x : H, HasSum (fun m : ℕ => ‖train m • x‖^2) (‖x‖^2)) ∧
    (∀ m n, train m * (starRingEnd ℂ) (train n) = (1-q)*a^m*b^n) ∧
    N*S=1 ∧ S*N=1 ∧ Z=F 0 ∧
    (∀ j, K j 0 * P = -(F j * P)) ∧
    (∀ n : ℕ, T (n+1) - q • T n - (if n=0 then q • Z else 0) =
      ((1-q)*b^(n+1)) • (F (n+1)*(1-P))) ∧
    (∀ n : ℕ, G n = b^(n+1) • F (n+1)) ∧
    ∀ M : ℕ, Z + ∑ n ∈ Finset.range M, G n =
      F 0 + ∑ n ∈ Finset.range M, b^(n+1) • F (n+1) := by
  let a := (r:ℂ)*(starRingEnd ℂ) u
  let b := (r:ℂ)*u
  let q := ((r^2 : ℝ):ℂ)
  let train := fun m : ℕ => ((Real.sqrt (1-r^2):ℝ):ℂ)*a^m
  let P := W.starProjection
  let E := fun m n : ℕ => ((1-q)*a^m*b^n) • (1-P) -
    (if m=0 ∧ n=0 then 1 else 0)
  let K := fun i j : ℕ => ∑ m ∈ Finset.range (i+1), F (i-m) * E m j
  let T := fun j : ℕ => K j j
  let N : H →L[ℂ] H := q • 1 + (1-q) • P
  let S : H →L[ℂ] H := q⁻¹ • (1-P)+P
  let Z := -(T 0*S)
  let C := fun i j : ℕ => ∑ m ∈ Finset.range (i+1),
    ((1-q)*a^m*b^j) • (F (i-m)*(1-P))
  let G := fun n : ℕ => (1-q)⁻¹ •
    (T (n+1) - q • T n - (if n=0 then q • Z else 0)) -
    b^(n+1) • (K (n+1) 0 * P)
  have hp : P*P=P := by
    ext x
    exact W.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  obtain ⟨hab, _, hsum⟩ := cell_circle_phases r hr hr' u hu
  have hq : q ≠ 0 := by dsimp [q]; exact_mod_cast (pow_ne_zero 2 hr.ne')
  have hqr : 1-r^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hr') (show 0 < 1+r by linarith)]
  have hq' : 1-q ≠ 0 := by dsimp [q]; exact_mod_cast hqr
  obtain ⟨hNS, hSN, _⟩ := cell_circle_inverse P hp q hq
  obtain ⟨hK,hC⟩ := circle_product_core a b q hab P F
  change (∀ i j, K i j=C i j - (if j=0 then F i else 0)) at hK
  change (∀ n, C (n+1) (n+1) = q • C n n + ((1-q)*b^(n+1)) • (F (n+1)*(1-P))) at hC
  have hzero : T 0 = -(F 0*N) := by
    change K 0 0 = _
    have hC00 : C 0 0 = (1-q) • (F 0*(1-P)) := by simp [C]
    rw [hK, hC00]; simp only [if_true, N, mul_add, mul_smul_comm, mul_one, mul_sub, smul_sub, sub_smul, one_smul]
    abel
  have hZ : Z=F 0 := by
    change -(T 0*S)=F 0
    rw [hzero, neg_mul, neg_neg, mul_assoc, hNS, mul_one]
  have hcolumn (j : ℕ) : K j 0 * P = -(F j*P) := by
    rw [hK]; simp only [if_true, sub_mul]
    have he : C j 0*P=0 := circle_idempotent_column a b q P hp F j
    rw [he, zero_sub]
  have hdiff (n : ℕ) : T (n+1)-q • T n-(if n=0 then q • Z else 0) =
      ((1-q)*b^(n+1)) • (F (n+1)*(1-P)) := by
    dsimp only [T]
    rw [hK,hK,hC,hZ]
    by_cases hn : n=0
    · subst n; simp [smul_sub]
    · simp [hn]
  have hG (n : ℕ) : G n = b^(n+1) • F (n+1) := by
    dsimp only [G]
    rw [hdiff,hcolumn,smul_smul,← mul_assoc,inv_mul_cancel₀ hq',one_mul,
      smul_neg,sub_neg_eq_add,← smul_add, mul_sub,mul_one,sub_add_cancel]
  have hqrle : 0 ≤ 1-r^2 := by nlinarith [mul_pos (sub_pos.mpr hr') (show 0 < 1+r by linarith)]
  have htrain (x : H) : HasSum (fun m : ℕ => ‖train m • x‖^2) (‖x‖^2) := by
    have hx := hsum.mul_right (‖x‖^2)
    rw [one_mul] at hx
    have he : (fun m : ℕ => ‖train m • x‖^2) =
        fun m : ℕ => ((1-r^2)*‖a‖^(2*m))*‖x‖^2 := by
      funext m
      simp only [train,norm_smul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hqrle,← pow_mul]
      rw [Nat.mul_comm m 2]
    rw [he]
    exact hx
  have hgram (m n : ℕ) : train m * (starRingEnd ℂ) (train n) = (1-q)*a^m*b^n := by
    have ha : (starRingEnd ℂ) a=b := by simp [a,b]
    have hs : (((Real.sqrt (1-r^2):ℝ):ℂ))^2 = 1-q := by
      dsimp [q]
      exact_mod_cast Real.sq_sqrt hqrle
    dsimp only [train]
    rw [map_mul,map_pow,ha,Complex.conj_ofReal]
    rw [← hs]
    ring
  refine ⟨htrain,hgram,hNS,hSN,hZ,hcolumn,hdiff,hG,?_⟩
  intro M
  change Z + ∑ n ∈ Finset.range M, G n = _
  rw [hZ]
  simp_rw [hG]
  rfl

#print axioms solution
