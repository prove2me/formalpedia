-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.optimality_conditions
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T00:12:01.887816+00:00
-- url     : https://prove2.me/submissions/375b4898-7b05-4056-8c2b-359c4173aff9

import Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_gradient
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_hessian
import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DerivativeTest

open Matrix MatrixCompletion.NoSpuriousMin

namespace OptAux

variable {d r : ℕ}

/-! ### Frobenius algebra -/

lemma frobSq_eq_innerM {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = innerM A A := by
  simp only [frobSq, innerM, sq]

lemma eq_zero_of_frobSq_eq_zero {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (h : frobSq A = 0) :
    A = 0 := by
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg (A k _)).mp h i (Finset.mem_univ i)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (A i l)).mp hi j
    (Finset.mem_univ j)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

lemma innerM_smul_left {m n : ℕ} (c : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    innerM (c • A) B = c * innerM A B := by
  simp only [innerM, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma innerM_add_left {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM (A + B) C = innerM A C + innerM B C := by
  simp only [innerM, Matrix.add_apply, add_mul, ← Finset.sum_add_distrib]

lemma innerM_add_right {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM A (B + C) = innerM A B + innerM A C := by
  simp only [innerM, Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

lemma innerM_neg_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    innerM (-A) B = -innerM A B := by
  simp only [innerM, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- `⟨M X, W⟩ = ⟨M, W Xᵀ⟩`. -/
lemma innerM_mul_transpose (M : Matrix (Fin d) (Fin d) ℝ) (X W : Matrix (Fin d) (Fin r) ℝ) :
    innerM (M * X) W = innerM M (W * Xᵀ) := by
  simp only [innerM, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma innerM_transpose (A B : Matrix (Fin d) (Fin d) ℝ) : innerM Aᵀ Bᵀ = innerM A B := by
  simp only [innerM, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma innerM_projSet_left (Ω : Finset (Fin d × Fin d)) (A B : Matrix (Fin d) (Fin d) ℝ) :
    innerM (projSet Ω A) B = innerM A (projSet Ω B) := by
  simp only [innerM, projSet, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (i, j) ∈ Ω <;> simp [h]

lemma projSet_idem (Ω : Finset (Fin d × Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (projSet Ω A) = projSet Ω A := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

lemma projSet_neg (Ω : Finset (Fin d × Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (-A) = -projSet Ω A := by
  ext i j
  by_cases h : (i, j) ∈ Ω <;> simp [projSet, h]

lemma projSet_transpose (Ω : Finset (Fin d × Fin d))
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω) (A : Matrix (Fin d) (Fin d) ℝ) :
    (projSet Ω A)ᵀ = projSet Ω Aᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, projSet, Matrix.of_apply]
  by_cases h : (i, j) ∈ Ω
  · simp [h, (hsym i j).mp h]
  · have h' : (j, i) ∉ Ω := fun hc => h ((hsym j i).mp hc)
    simp [h, h']

/-! ### Translating a derivative along a line -/

lemma hasDerivAt_of_shift {φ : ℝ → ℝ} {L s : ℝ} (h : HasDerivAt (fun u => φ (s + u)) L 0) :
    HasDerivAt φ L s := by
  have hs : HasDerivAt (fun x : ℝ => x - s) 1 s := (hasDerivAt_id s).sub_const s
  have h' : HasDerivAt (fun u : ℝ => φ (s + u)) L ((fun x : ℝ => x - s) s) := by simpa using h
  have h2 : HasDerivAt ((fun u : ℝ => φ (s + u)) ∘ fun x : ℝ => x - s) (L * 1) s :=
    HasDerivAt.comp s h' hs
  have hfun : ((fun u : ℝ => φ (s + u)) ∘ fun x : ℝ => x - s) = φ := by
    funext x; simp
  rw [hfun] at h2
  simpa using h2

/-! ### A local minimum has nonnegative second derivative -/

lemma secondDeriv_nonneg_of_isLocalMin {f G : ℝ → ℝ} {L : ℝ}
    (hmin : IsLocalMin f 0) (hf : ∀ s, HasDerivAt f (G s) s)
    (hG0 : G 0 = 0) (hG : HasDerivAt G L 0) : 0 ≤ L := by
  by_contra hneg
  push_neg at hneg
  have hderivG : deriv G 0 = L := hG.deriv
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg (f := G) (x₀ := 0)
    (by rw [hderivG]; exact hneg) hG0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsign
  obtain ⟨η, hη, hmem⟩ := Metric.eventually_nhds_iff.mp hmin
  set δ := min (ε / 2) (η / 2) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hGneg : ∀ x ∈ Set.Ioo (0 : ℝ) δ, deriv f x < 0 := by
    intro x hx
    have hxb : dist x 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
      calc x < δ := hx.2
        _ ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    have hsx : SignType.sign (G x) = SignType.sign (0 - x) := hball hxb
    rw [sign_neg (by linarith [hx.1] : (0 : ℝ) - x < 0)] at hsx
    have : G x < 0 := by rwa [sign_eq_neg_one_iff] at hsx
    rwa [(hf x).deriv]
  have hcont : ContinuousOn f (Set.Icc 0 δ) := fun x _ => ((hf x).continuousAt).continuousWithinAt
  have hanti : StrictAntiOn f (Set.Icc 0 δ) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 δ) hcont fun x hx => ?_
    rw [interior_Icc] at hx
    exact hGneg x hx
  have hlt : f δ < f 0 :=
    hanti (Set.left_mem_Icc.mpr hδpos.le) (Set.right_mem_Icc.mpr hδpos.le) hδpos
  have hge : f 0 ≤ f δ := by
    refine hmem ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]
    calc δ ≤ η / 2 := min_le_right _ _
      _ < η := by linarith
  linarith

end OptAux

open OptAux

theorem solution {d r : ℕ} (Z X : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ) (hlam : 0 ≤ lam) (hα : 0 < α)
    (hsym : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω)
    (hmin : IsLocalMin (objective Z Ω lam α) X) :
    FirstOrderPt Z Ω lam α X ∧ SecondOrderPt Z Ω lam α X := by
  classical
  have main : ∀ V : Matrix (Fin d) (Fin r) ℝ,
      innerM (objGrad Z Ω lam α X) V = 0 ∧
        2 * innerM (projSet Ω (Z * Zᵀ - X * Xᵀ)) (V * Vᵀ)
          ≤ frobSq (projSet Ω (V * Xᵀ + X * Vᵀ)) + lam * regHessQF α X V := by
    intro V
    set A := projSet Ω (Z * Zᵀ - X * Xᵀ) with hA
    set B := projSet Ω (V * Xᵀ + X * Vᵀ) with hB
    set C := projSet Ω (V * Vᵀ) with hC
    -- Entrywise expansion of the residual along the line.
    have hentry : ∀ (s : ℝ) (i j : Fin d),
        ((X + s • V) * (X + s • V)ᵀ) i j
          = (X * Xᵀ) i j + s * ((V * Xᵀ + X * Vᵀ) i j) + s ^ 2 * ((V * Vᵀ) i j) := by
      intro s i j
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
        smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hproj : ∀ (s : ℝ) (i j : Fin d),
        projSet Ω (Z * Zᵀ - (X + s • V) * (X + s • V)ᵀ) i j
          = A i j - s * B i j - s ^ 2 * C i j := by
      intro s i j
      simp only [hA, hB, hC, projSet, Matrix.of_apply, Matrix.sub_apply, hentry s i j]
      by_cases h : (i, j) ∈ Ω
      · simp only [if_pos h]; ring
      · simp only [if_neg h]; ring
    -- The smooth part of the objective is a quartic polynomial in `s`.
    have hquart : ∀ s : ℝ,
        frobSq (projSet Ω (Z * Zᵀ - (X + s • V) * (X + s • V)ᵀ))
          = frobSq A + (-(2 * innerM A B)) * s
            + (frobSq B - 2 * innerM A C) * s ^ 2
            + 2 * innerM B C * s ^ 3 + frobSq C * s ^ 4 := by
      intro s
      simp only [frobSq, innerM, hproj s, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    set P : ℝ → ℝ := fun u =>
      (frobSq A + (-(2 * innerM A B)) * u + (frobSq B - 2 * innerM A C) * u ^ 2
        + 2 * innerM B C * u ^ 3 + frobSq C * u ^ 4) / 2 with hP
    set P' : ℝ → ℝ := fun u =>
      ((-(2 * innerM A B)) * 1 + (frobSq B - 2 * innerM A C) * (2 * u)
        + 2 * innerM B C * (3 * u ^ 2) + frobSq C * (4 * u ^ 3)) / 2 with hP'
    have hPderiv : ∀ s : ℝ, HasDerivAt P (P' s) s := by
      intro s
      have h1 : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
      have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * s ^ 2) s := by
        simpa using hasDerivAt_pow 3 s
      have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * s ^ 3) s := by
        simpa using hasDerivAt_pow 4 s
      have hN := ((((hasDerivAt_const s (frobSq A)).add
        (h1.const_mul (-(2 * innerM A B)))).add
        (h2.const_mul (frobSq B - 2 * innerM A C))).add
        (h3.const_mul (2 * innerM B C))).add (h4.const_mul (frobSq C))
      simpa [hP, hP'] using hN.div_const 2
    have hP'deriv : HasDerivAt P' (frobSq B - 2 * innerM A C) 0 := by
      have h1 : HasDerivAt (fun u : ℝ => u) 1 (0 : ℝ) := hasDerivAt_id 0
      have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (0 : ℝ) 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (0 : ℝ) 0 := by
        simpa using hasDerivAt_pow 3 (0 : ℝ)
      have hN := (((hasDerivAt_const (0 : ℝ) ((-(2 * innerM A B)) * 1)).add
        ((h1.const_mul (2 : ℝ)).const_mul (frobSq B - 2 * innerM A C))).add
        ((h2.const_mul (3 : ℝ)).const_mul (2 * innerM B C))).add
        ((h3.const_mul (4 : ℝ)).const_mul (frobSq C))
      have := hN.div_const 2
      simpa [hP'] using this
    -- The objective along the line.
    have hobj : (fun u : ℝ => objective Z Ω lam α (X + u • V))
        = fun u : ℝ => P u + lam * reg α (X + u • V) := by
      funext u
      rw [objective, hquart u]
    have hregderiv : ∀ s : ℝ,
        HasDerivAt (fun u : ℝ => reg α (X + u • V)) (innerM (regGrad α (X + s • V)) V) s := by
      intro s
      refine hasDerivAt_of_shift ?_
      have h := MatrixCompletion.NoSpuriousMin.regularizer_gradient α hα (X + s • V) V
      have e : ∀ u : ℝ, X + s • V + u • V = X + (s + u) • V := by
        intro u; rw [add_smul]; abel
      simpa [e] using h
    have hgderiv : ∀ s : ℝ, HasDerivAt (fun u : ℝ => objective Z Ω lam α (X + u • V))
        (P' s + lam * innerM (regGrad α (X + s • V)) V) s := by
      intro s
      rw [hobj]
      exact (hPderiv s).add ((hregderiv s).const_mul lam)
    have hlinemin : IsLocalMin (fun u : ℝ => objective Z Ω lam α (X + u • V)) 0 := by
      have hcont : Continuous fun u : ℝ => X + u • V := by fun_prop
      have hmin' : IsLocalMin (objective Z Ω lam α) ((fun u : ℝ => X + u • V) 0) := by
        have hz : (fun u : ℝ => X + u • V) 0 = X := by simp
        rw [hz]; exact hmin
      have hres := IsLocalMin.comp_continuous (f := objective Z Ω lam α)
        (g := fun u : ℝ => X + u • V) (b := (0 : ℝ)) hmin' hcont.continuousAt
      exact hres
    -- First-order condition.
    have hfirst : P' 0 + lam * innerM (regGrad α X) V = 0 := by
      have h := hlinemin.hasDerivAt_eq_zero (hgderiv 0)
      simpa using h
    -- Identify `P' 0` with the gradient pairing.
    have hAsymm : Aᵀ = A := by
      rw [hA, projSet_transpose Ω hsym]
      congr 1
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.transpose_transpose]
    have hAB : innerM A B = 2 * innerM A (V * Xᵀ) := by
      rw [hB, ← innerM_projSet_left, hA, projSet_idem, ← hA, innerM_add_right]
      have hswap : innerM A (X * Vᵀ) = innerM A (V * Xᵀ) := by
        have h1 := innerM_transpose A (V * Xᵀ)
        rw [hAsymm, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
        exact h1
      rw [hswap]; ring
    have hP'0 : P' 0 = -innerM A B := by rw [hP']; ring
    have hnegA : projSet Ω (X * Xᵀ - Z * Zᵀ) = -A := by
      rw [hA, ← projSet_neg]
      congr 1
      abel
    have hgrad : innerM (objGrad Z Ω lam α X) V = P' 0 + lam * innerM (regGrad α X) V := by
      rw [objGrad, innerM_add_left, innerM_smul_left, innerM_smul_left, innerM_mul_transpose,
        hnegA, innerM_neg_left, hP'0, hAB]
      ring
    -- Second-order condition.
    have hsecond : 0 ≤ (frobSq B - 2 * innerM A C) + lam * regHessQF α X V := by
      refine secondDeriv_nonneg_of_isLocalMin hlinemin hgderiv ?_ ?_
      · simpa using hfirst
      · have hch := MatrixCompletion.NoSpuriousMin.regularizer_hessian α hα X V
        exact hP'deriv.add (hch.const_mul lam)
    have hAC : innerM A C = innerM A (V * Vᵀ) := by
      rw [hC, ← innerM_projSet_left, hA, projSet_idem]
    exact ⟨by linarith [hgrad, hfirst], by linarith [hsecond, hAC]⟩
  refine ⟨?_, ?_⟩
  · have h : frobSq (objGrad Z Ω lam α X) = 0 := by
      rw [frobSq_eq_innerM]; exact (main _).1
    exact eq_zero_of_frobSq_eq_zero h
  · intro V
    exact (main V).2
