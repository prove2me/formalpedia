-- Prove2me | solution 1 for IntegerRootsFN.Main.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:03.026968+00:00
-- url     : https://prove2.me/submissions/333e245e-024d-417b-a04c-9d1f9131f1f7

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

open Polynomial IntegerRootsFN.Main

private theorem coeff_zero_of_not_mem_support (p : Polynomial ℂ) {j : ℕ}
    (hj : j ∉ p.support) : p.coeff j = 0 := by
  by_contra hne
  exact hj (Polynomial.mem_support_iff.mpr hne)

private theorem norm_coeff_le_normOne (p : Polynomial ℂ) (j : ℕ) :
    ‖p.coeff j‖ ≤ normOne p := by
  classical
  by_cases hj : j ∈ p.support
  · exact Finset.single_le_sum (fun i _ => norm_nonneg _) hj
  · rw [coeff_zero_of_not_mem_support p hj, norm_zero]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg _)

private theorem sum_sq_le_sq_sum_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) : (∑ i ∈ s, x i ^ 2) ≤ (∑ i ∈ s, x i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
    simp only [Finset.sum_insert ha]
    nlinarith [ih hxs]

private theorem normTwo_le_normOne (p : Polynomial ℂ) : normTwo p ≤ normOne p := by
  classical
  unfold normTwo normOne
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  exact sum_sq_le_sq_sum_nonneg _ _ (fun _ _ => norm_nonneg _)

private theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 <= y i) :
    √(∑ i ∈ s, (x i + y i) ^ 2) ≤ √(∑ i ∈ s, x i ^ 2) + √(∑ i ∈ s, y i ^ 2) := by
  classical
  have hx0 : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hy0 : 0 ≤ ∑ i ∈ s, y i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC0 : 0 ≤ ∑ i ∈ s, x i * y i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hx i hi) (hy i hi))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hCsq : (∑ i ∈ s, x i * y i) ^ 2 ≤
      (√(∑ i ∈ s, x i ^ 2) * √(∑ i ∈ s, y i ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt hy0]
    exact hc
  have hC : (∑ i ∈ s, x i * y i) ≤
      √(∑ i ∈ s, x i ^ 2) * √(∑ i ∈ s, y i ^ 2) :=
    (sq_le_sq₀ hC0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hCsq
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  calc
    (∑ i ∈ s, (x i + y i) ^ 2) =
        (∑ i ∈ s, x i ^ 2) + (∑ i ∈ s, y i ^ 2) + 2 * ∑ i ∈ s, x i * y i := by
      simp only [add_sq, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      ring
    _ ≤ _ := by nlinarith

private theorem normTwo_add_le (p q : Polynomial ℂ) :
    normTwo (p + q) ≤ normTwo p + normTwo q := by
  classical
  let s := p.support ∪ q.support
  have hp : normTwo p = √(∑ i ∈ s, ‖p.coeff i‖ ^ 2) := by
    unfold normTwo
    congr 1
    apply Finset.sum_subset (Finset.subset_union_left)
    intro i _ hi
    simp [coeff_zero_of_not_mem_support p hi]
  have hq : normTwo q = √(∑ i ∈ s, ‖q.coeff i‖ ^ 2) := by
    unfold normTwo
    congr 1
    apply Finset.sum_subset (Finset.subset_union_right)
    intro i _ hi
    simp [coeff_zero_of_not_mem_support q hi]
  have hpq : normTwo (p + q) = √(∑ i ∈ s, ‖p.coeff i + q.coeff i‖ ^ 2) := by
    unfold normTwo
    congr 1
    apply Finset.sum_subset (by
      intro i hi
      have hc : p.coeff i + q.coeff i ≠ 0 := by simpa using hi
      by_contra his
      simp only [s, Finset.mem_union, not_or] at his
      exact hc (by rw [coeff_zero_of_not_mem_support p his.1,
        coeff_zero_of_not_mem_support q his.2, add_zero]))
    intro i _ hi
    simp [coeff_zero_of_not_mem_support (p + q) hi]
  rw [hp, hq, hpq]
  calc
    √(∑ i ∈ s, ‖p.coeff i + q.coeff i‖ ^ 2)
        ≤ √(∑ i ∈ s, (‖p.coeff i‖ + ‖q.coeff i‖) ^ 2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro i _
          exact sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr
            (norm_add_le _ _)
    _ ≤ _ := sqrt_sum_sq_add_le s _ _ (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)

private theorem normTwo_le_of_natDegree_le (p : Polynomial ℂ) {d : ℕ}
    (hdeg : p.natDegree ≤ d) {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ j : ℕ, ‖p.coeff j‖ ≤ B) : normTwo p ≤ B * √((d : ℝ) + 1) := by
  classical
  have hsub : p.support ⊆ Finset.range (d + 1) := by
    intro j hj
    rw [Finset.mem_range]
    have hne := Polynomial.mem_support_iff.mp hj
    have := Polynomial.le_natDegree_of_ne_zero hne
    omega
  have heq : normTwo p = √(∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖ ^ 2) := by
    unfold normTwo
    congr 1
    apply Finset.sum_subset hsub
    intro j _ hj
    simp [coeff_zero_of_not_mem_support p hj]
  rw [heq]
  calc
    √(∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖ ^ 2)
        ≤ √(∑ _j ∈ Finset.range (d + 1), B ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.sum_le_sum (fun j _ =>
            (sq_le_sq₀ (norm_nonneg _) hB).mpr (hcoeff j))
    _ = B * √((d : ℝ) + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [mul_comm, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
      norm_num

private theorem mahler_factorPolynomial {d : ℕ} (c : ℂ) (β : Fin d → ℂ) :
    (factorPolynomial c β).mahlerMeasure = ‖c‖ * ∏ i, max 1 ‖β i‖ := by
  classical
  unfold factorPolynomial
  rw [Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_const]
  congr 1
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.mahlerMeasure_mul,
      ih, Polynomial.mahlerMeasure_X_sub_C]

private theorem eval_factorPolynomial {d : ℕ} (c : ℂ) (β : Fin d → ℂ) (α : ℂ) :
    (factorPolynomial c β).eval α = c * ∏ i, (α - β i) := by
  classical
  unfold factorPolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.eval_mul, ih]
    simp

private theorem normOne_eq_sum_range (p : Polynomial ℂ) {d : ℕ} (hdeg : p.natDegree ≤ d) :
    normOne p = ∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖ := by
  classical
  unfold normOne
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range]
    have := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
    omega
  · intro j _ hj
    simp [coeff_zero_of_not_mem_support p hj]

private theorem norm_eval_le_normOne_mul (p : Polynomial ℂ) {d : ℕ}
    (hdeg : p.natDegree ≤ d) (z : ℂ) :
    ‖p.eval z‖ ≤ normOne p * (max 1 ‖z‖) ^ d := by
  classical
  rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < d + 1), normOne_eq_sum_range p hdeg]
  calc
    ‖∑ i ∈ Finset.range (d + 1), p.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range (d + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖ * (max 1 ‖z‖) ^ d := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ‖z‖ ^ i ≤ (max 1 ‖z‖) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
        _ ≤ (max 1 ‖z‖) ^ d :=
          pow_le_pow_right₀ (le_max_left _ _) (by simp at hi; omega)
    _ = (∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖) * (max 1 ‖z‖) ^ d := by
      rw [Finset.sum_mul]

private theorem root_factor_estimate {α z : ℂ}
    (hfar : (1 : ℝ) / 8 ≤ ‖α - z‖) :
    max 1 ‖α‖ ≤ 9 * ‖α - z‖ * max 1 ‖z‖ := by
  have hB : 1 ≤ max 1 ‖z‖ := le_max_left _ _
  have hD : 0 ≤ ‖α - z‖ := norm_nonneg _
  have hαz : ‖α‖ ≤ ‖z‖ + ‖α - z‖ := by
    calc ‖α‖ = ‖z + (α - z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hfirst : max 1 ‖α‖ ≤ max 1 ‖z‖ * (1 + ‖α - z‖) := by
    rcases le_total ‖α‖ 1 with ha | ha
    · rw [max_eq_left ha]
      nlinarith [mul_le_mul_of_nonneg_right hB hD]
    · rw [max_eq_right ha]
      have hz : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hB hD]
  have hsecond : max 1 ‖z‖ * (1 + ‖α - z‖) ≤
      9 * ‖α - z‖ * max 1 ‖z‖ := by
    nlinarith [mul_nonneg (norm_nonneg (α - z)) (sub_nonneg.mpr hB)]
  exact hfirst.trans hsecond

namespace IntegerRootsFN.Main

private theorem solution_aux (d b : ℕ) (g : Polynomial ℤ) (hg : Valid g d b)
    (ĝ : Polynomial ℂ) (hdegree : ĝ.natDegree = d) (β : Fin d → ℂ)
    (hβ : ListsRoots ĝ β)
    (hδ : normOne (ĝ - complexify g) < perturbationThreshold d b) :
    CoversRoots (complexify g) β ∧ logRootSize β ≤ rootSizeBound d b := by
  classical
  let G : Polynomial ℂ := complexify g
  let E : Polynomial ℂ := ĝ - G
  let δ : ℝ := normOne E
  let S : ℝ := (2 : ℝ) ^ b * √((d : ℝ) + 1)
  let P : ℝ := ∏ i, max 1 ‖β i‖
  have hd : 1 ≤ d := hg.1
  have hb : 1 ≤ b := hg.2.1
  have hgdeg : g.natDegree = d := hg.2.2.1
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hGdeg : G.natDegree = d := Polynomial.natDegree_map_eq_of_injective hinj g |>.trans hgdeg
  have hEdeg : E.natDegree ≤ d := by
    apply (Polynomial.natDegree_sub_le ĝ G).trans
    simp [G, hdegree, hGdeg]
  have hGb : ∀ j : ℕ, ‖G.coeff j‖ < (2 : ℝ) ^ b := by
    intro j
    have hj : |g.coeff j| < (2 : ℤ) ^ b := hg.2.2.2.2 j
    have hj' : (‖G.coeff j‖ : ℝ) = |(g.coeff j : ℝ)| := by
      simp [G, complexify]
    rw [hj']
    exact_mod_cast hj
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hS1 : 1 ≤ S := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    have hs : (1 : ℝ) ≤ √((d : ℝ) + 1) := by
      rw [show (1 : ℝ) = √(1 : ℝ) by simp]
      apply Real.sqrt_le_sqrt
      norm_num
    dsimp [S]
    nlinarith
  have hGS : normTwo G ≤ S := by
    exact (normTwo_le_of_natDegree_le G (le_of_eq hGdeg) (by positivity)
      (fun j => (hGb j).le))
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, normOne]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδsmall : δ < 1 / (8 * (9 : ℝ) ^ d * (S + 1)) := by
    exact hδ
  have hQ : 0 < 8 * (9 : ℝ) ^ d * (S + 1) := by positivity
  have hδQ : δ * (8 * (9 : ℝ) ^ d * (S + 1)) < 1 :=
    (lt_div_iff₀ hQ).mp hδsmall
  have hδhalf : δ < 1 / 2 := by
    have h9 : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_pos hS hS]
  have hM : ĝ.mahlerMeasure = ‖ĝ.leadingCoeff‖ * P := by
    calc
      ĝ.mahlerMeasure = (factorPolynomial ĝ.leadingCoeff β).mahlerMeasure := congrArg _ hβ
      _ = _ := mahler_factorPolynomial _ _
  have hlandau : ĝ.mahlerMeasure ≤ normTwo ĝ :=
    Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff ĝ
  have hnormTwo : normTwo ĝ ≤ S + δ := by
    calc
      normTwo ĝ = normTwo (G + E) := by congr 1; dsimp [E]; abel
      _ ≤ normTwo G + normTwo E := normTwo_add_le _ _
      _ ≤ normTwo G + normOne E := add_le_add le_rfl (normTwo_le_normOne E)
      _ ≤ S + δ := add_le_add hGS le_rfl
  have hMle : ĝ.mahlerMeasure ≤ S + δ := hlandau.trans hnormTwo
  have hGlc : 1 ≤ ‖G.leadingCoeff‖ := by
    have hgne : g ≠ 0 := by
      intro hzero
      have hz := hg.2.2.2.1
      simp [hzero] at hz
    have hlead : G.leadingCoeff = (g.leadingCoeff : ℂ) := by
      simp [G, complexify, Polynomial.leadingCoeff_map_of_injective hinj]
    rw [hlead, ← norm_natAbs, Complex.norm_natCast]
    have hn : 1 ≤ g.leadingCoeff.natAbs := by
      have := Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hgne)
      omega
    exact_mod_cast hn
  have hclead : (1 : ℝ) / 2 < ‖ĝ.leadingCoeff‖ := by
    have hc : ‖E.coeff d‖ ≤ δ := norm_coeff_le_normOne E d
    have hc' : ‖G.leadingCoeff - ĝ.leadingCoeff‖ ≤ δ := by
      rw [show G.leadingCoeff = G.coeff d by simp [Polynomial.leadingCoeff, hGdeg],
        show ĝ.leadingCoeff = ĝ.coeff d by simp [Polynomial.leadingCoeff, hdegree]]
      simpa [E, norm_sub_rev] using hc
    have htri : ‖G.leadingCoeff‖ ≤ ‖ĝ.leadingCoeff‖ + δ := by
      calc
        ‖G.leadingCoeff‖ = ‖ĝ.leadingCoeff + (G.leadingCoeff - ĝ.leadingCoeff)‖ := by
          congr 1
          abel
        _ ≤ ‖ĝ.leadingCoeff‖ + ‖G.leadingCoeff - ĝ.leadingCoeff‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl hc'
    linarith
  have hP0 : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hP2 : P ≤ 2 * (S + δ) := by
    have h := hMle
    rw [hM] at h
    nlinarith [mul_pos hP0 hP0]
  constructor
  · intro α hα
    by_contra hnear
    have hfar : ∀ i, (1 : ℝ) / 8 ≤ ‖α - β i‖ := by
      intro i
      exact le_of_not_gt (fun h => hnear ⟨i, h⟩)
    let A : ℝ := max 1 ‖α‖
    let D : Fin d → ℝ := fun i => ‖α - β i‖
    let B : Fin d → ℝ := fun i => max 1 ‖β i‖
    have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hD0 : ∀ i, 0 ≤ D i := fun _ => norm_nonneg _
    have hB0 : ∀ i, 0 ≤ B i := fun i => le_trans (norm_nonneg (β i)) (le_max_right _ _)
    have hpoint : ∀ i, A ≤ 9 * D i * B i := fun i => root_factor_estimate (hfar i)
    have hprod : A ^ d ≤ (9 : ℝ) ^ d * (∏ i, D i) * P := by
      calc
        A ^ d = ∏ _i : Fin d, A := by simp
        _ ≤ ∏ i, (9 * D i * B i) := by
          exact Finset.prod_le_prod (fun _ _ => hA.le) (fun i _ => hpoint i)
        _ = (9 : ℝ) ^ d * (∏ i, D i) * P := by
          simp only [P, B, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
    have heqval : ĝ.eval α = ĝ.leadingCoeff * ∏ i, (α - β i) := by
      calc
        ĝ.eval α = (factorPolynomial ĝ.leadingCoeff β).eval α := congrArg (Polynomial.eval α) hβ
        _ = _ := eval_factorPolynomial _ _ _
    have heval : ‖ĝ.eval α‖ = ‖ĝ.leadingCoeff‖ * ∏ i, D i := by
      rw [heqval, norm_mul]
      simp [D]
    have hDprod : (∏ i, D i) ≤ 2 * ‖ĝ.eval α‖ := by
      rw [heval]
      have hp : 0 ≤ ∏ i, D i := Finset.prod_nonneg (fun i _ => hD0 i)
      nlinarith
    have hBP : P ≤ 2 * (S + δ) := hP2
    have hlower : A ^ d ≤ 4 * (9 : ℝ) ^ d * (S + δ) * ‖ĝ.eval α‖ := by
      have hp : 0 ≤ ∏ i, D i := Finset.prod_nonneg (fun i _ => hD0 i)
      have hN : 0 ≤ (9 : ℝ) ^ d := by positivity
      calc
        A ^ d ≤ (9 : ℝ) ^ d * (∏ i, D i) * P := hprod
        _ ≤ (9 : ℝ) ^ d * (2 * ‖ĝ.eval α‖) * (2 * (S + δ)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hDprod hN) hBP hP0.le
            (mul_nonneg hN (by positivity))
        _ = _ := by ring
    have hEeval : ‖E.eval α‖ ≤ δ * A ^ d := norm_eval_le_normOne_mul E hEdeg α
    have hGeval : G.eval α = 0 := hα
    have heq : ĝ.eval α = E.eval α := by
      dsimp [E]
      simp [hGeval]
    rw [heq] at hlower
    have hmain : A ^ d ≤ (4 * (9 : ℝ) ^ d * (S + δ) * δ) * A ^ d := by
      calc
        A ^ d ≤ 4 * (9 : ℝ) ^ d * (S + δ) * ‖E.eval α‖ := hlower
        _ ≤ 4 * (9 : ℝ) ^ d * (S + δ) * (δ * A ^ d) := by
          exact mul_le_mul_of_nonneg_left hEeval (by positivity)
        _ = _ := by ring
    have hcontra_lower : 1 ≤ 4 * (9 : ℝ) ^ d * (S + δ) * δ := by
      have hApos : 0 < A ^ d := pow_pos hA _
      have ht : A ^ d * 1 ≤ A ^ d * (4 * (9 : ℝ) ^ d * (S + δ) * δ) := by
        simpa [mul_comm] using hmain
      exact (mul_le_mul_iff_right₀ hApos).mp ht
    have hSδ : S + δ < S + 1 := by linarith
    have hprodlt : δ * (S + δ) < (1 / (8 * (9 : ℝ) ^ d * (S + 1))) * (S + 1) := by
      calc
        δ * (S + δ) < (1 / (8 * (9 : ℝ) ^ d * (S + 1))) * (S + δ) :=
          mul_lt_mul_of_pos_right hδsmall (by positivity)
        _ ≤ (1 / (8 * (9 : ℝ) ^ d * (S + 1))) * (S + 1) :=
          mul_le_mul_of_nonneg_left hSδ.le (by positivity)
    have hcontra_upper : 4 * (9 : ℝ) ^ d * (S + δ) * δ < 1 / 2 := by
      calc
        4 * (9 : ℝ) ^ d * (S + δ) * δ = 4 * (9 : ℝ) ^ d * (δ * (S + δ)) := by ring
        _ < 4 * (9 : ℝ) ^ d * ((1 / (8 * (9 : ℝ) ^ d * (S + 1))) * (S + 1)) := by
          exact mul_lt_mul_of_pos_left hprodlt (by positivity)
        _ = 1 / 2 := by
          field_simp
          ring
    linarith
  · have hP4 : P ≤ 4 * S := by
      have hδ1 : δ < 1 := by linarith
      nlinarith
    have hlogprod : Real.log P = ∑ i, Real.log (max 1 ‖β i‖) := by
      dsimp [P]
      apply Real.log_prod
      intro i _
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hlog : Real.log P ≤ Real.log 2 * rootSizeBound d b := by
      calc
        Real.log P ≤ Real.log (4 * S) := Real.log_le_log hP0 hP4
        _ = Real.log 2 * rootSizeBound d b := by
          dsimp [S]
          unfold rootSizeBound logTwo
          rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < (2 : ℝ) ^ b * √((d : ℝ) + 1))),
            Real.log_mul (by positivity) (by positivity),
            Real.log_sqrt (by positivity), Real.log_pow]
          have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            norm_num
          rw [h4]
          field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
          ring
    unfold logRootSize logTwo
    rw [← Finset.sum_div, ← hlogprod]
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr (by simpa [mul_comm] using hlog)

end IntegerRootsFN.Main

theorem solution (d b : ℕ) (g : Polynomial ℤ) (hg : Valid g d b)
    (ĝ : Polynomial ℂ) (hdegree : ĝ.natDegree = d) (β : Fin d → ℂ)
    (hβ : ListsRoots ĝ β)
    (hδ : normOne (ĝ - complexify g) < perturbationThreshold d b) :
    CoversRoots (complexify g) β ∧ logRootSize β ≤ rootSizeBound d b := by
  exact IntegerRootsFN.Main.solution_aux d b g hg ĝ hdegree β hβ hδ
