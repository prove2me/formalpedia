-- Prove2me | solution 1 for LinearOptimization.simplex_terminal_classification
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:52:14.818359+00:00
-- url     : https://prove2.me/submissions/dc0e8024-9a5a-458c-8a0c-d75099aa1421

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_LinearOptimization_OptimalBasis
import Theorems.Thm_LinearOptimization_simplex_reduced_cost_optimality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

private lemma basicDirection_entering {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    (hj : j ∉ Set.range B) :
    LinearOptimization.basicDirection A B j j = 1 := by
  classical
  unfold LinearOptimization.basicDirection
  simp only [Pi.sub_apply, Pi.single_apply, Finset.sum_apply]
  have hsum : (∑ i : Fin m, (if j = B i then
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r j)) i else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hji : j ≠ B i := by
      intro h
      exact hj ⟨i, h.symm⟩
    simp [hji]
  simp [hsum]

private lemma basicDirection_basic {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    (hj : j ∉ Set.range B) (i : Fin m) :
    LinearOptimization.basicDirection A B j (B i) =
      -LinearOptimization.pivotColumn A B j i := by
  classical
  have hji : j ≠ B i := by
    intro h
    apply hj
    exact ⟨i, h.symm⟩
  unfold LinearOptimization.basicDirection LinearOptimization.pivotColumn
  simp [Pi.single_apply, hji, B.injective.eq_iff]

private lemma basicDirection_other {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j k : Fin n)
    (hkj : k ≠ j) (hkB : k ∉ Set.range B) :
    LinearOptimization.basicDirection A B j k = 0 := by
  classical
  unfold LinearOptimization.basicDirection
  simp only [Pi.sub_apply, Pi.single_apply, Finset.sum_apply]
  have hsum : (∑ i : Fin m, (if k = B i then
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun r => A r j)) i else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hki : k ≠ B i := by
      intro h
      exact hkB ⟨i, h.symm⟩
    simp [hki]
  simp [hkj, hsum]

private lemma basicDirection_kernel {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (j : Fin n)
    [Invertible (LinearOptimization.basisMatrix A B)] :
    A.mulVec (LinearOptimization.basicDirection A B j) = 0 := by
  classical
  unfold LinearOptimization.basicDirection
  change A.mulVec (Pi.single j 1 - ∑ i : Fin m,
    Pi.single (B i) (LinearOptimization.pivotColumn A B j i)) = 0
  rw [Matrix.mulVec_sub, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_single]
  have hsum : (∑ i : Fin m,
      MulOpposite.op (LinearOptimization.pivotColumn A B j i) • A.col (B i)) =
      (LinearOptimization.basisMatrix A B).mulVec
        (LinearOptimization.pivotColumn A B j) := by
    funext r
    simp [Matrix.mulVec, dotProduct, LinearOptimization.basisMatrix,
      LinearOptimization.pivotColumn, Matrix.col, mul_comm]
  rw [hsum]
  unfold LinearOptimization.pivotColumn
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
  ext r
  simp [Matrix.mulVec, Matrix.one_apply, Matrix.col]

private lemma dot_basicDirection_eq_reducedCost {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) :
    c ⬝ᵥ LinearOptimization.basicDirection A B j =
      LinearOptimization.reducedCost A c B j := by
  classical
  unfold LinearOptimization.basicDirection LinearOptimization.reducedCost
  rw [dotProduct_sub, dotProduct_sum, dotProduct_single]
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_single]
  unfold dotProduct
  ring

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (hstate : LinearOptimization.IsSimplexState A b B x)
    (hterminal : ¬∃ (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ),
      LinearOptimization.IsSimplexPivot A c B x B' x') :
    (LinearOptimization.IsOptimalBasis A b c B ∧
      LinearOptimization.IsLpOptimal c (LinearOptimization.stdPolyhedron A b) x) ∨
      ∃ d : Fin n → ℝ, A.mulVec d = 0 ∧ 0 ≤ d ∧ c ⬝ᵥ d < 0 ∧
        LinearOptimization.lpValue c (LinearOptimization.stdPolyhedron A b) = ⊥ := by
  classical
  rcases hstate with ⟨hB, hx, hxB⟩
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    exact hB
  letI : Invertible (LinearOptimization.basisMatrix A B) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols).invertible
  by_cases hrc : ∀ j, 0 ≤ LinearOptimization.reducedCost A c B j
  · left
    have hopt :=
      (LinearOptimization.simplex_reduced_cost_optimality
        A b c hA B hB x hx hxB).1 hrc
    have hBMx : (LinearOptimization.basisMatrix A B).mulVec
        (fun i => x (B i)) = b := by
      funext i
      change (∑ k : Fin m, A i (B k) * x (B k)) = b i
      have himage : (∑ k : Fin m, A i (B k) * x (B k)) =
          ∑ j ∈ Finset.univ.image B, A i j * x j := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => B.injective h
      rw [himage]
      have hall : (∑ j ∈ Finset.univ.image B, A i j * x j) =
          ∑ j : Fin n, A i j * x j := by
        apply Finset.sum_subset (by intro j hj; simp)
        intro j _ hj
        have hjrange : j ∉ Set.range B := by
          intro hr
          obtain ⟨k, rfl⟩ := hr
          exact hj (by simp)
        rw [hxB j hjrange, mul_zero]
      rw [hall]
      simpa [Matrix.mulVec, dotProduct] using congrFun hx.1 i
    have hxb : (LinearOptimization.basisMatrix A B)⁻¹.mulVec b =
        (fun i => x (B i)) := by
      rw [← hBMx, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible]
      simp
    refine ⟨⟨hB, ?_, hrc⟩, hopt⟩
    rw [hxb]
    exact fun i => hx.2 (B i)
  · push_neg at hrc
    obtain ⟨j, hcj⟩ := hrc
    have hj : j ∉ Set.range B := by
      intro hjrange
      obtain ⟨i, rfl⟩ := hjrange
      rw [LinearOptimization.reducedCost_basic] at hcj
      linarith
    by_cases hpositive : ∃ i, 0 < LinearOptimization.pivotColumn A B j i
    · let s : Finset (Fin m) :=
        Finset.univ.filter (fun i => 0 < LinearOptimization.pivotColumn A B j i)
      have hs : s.Nonempty := by
        obtain ⟨i, hi⟩ := hpositive
        exact ⟨i, by simp [s, hi]⟩
      obtain ⟨ℓ, hℓs, hmin⟩ := Finset.exists_min_image s
        (fun i => x (B i) / LinearOptimization.pivotColumn A B j i) hs
      have hℓ : 0 < LinearOptimization.pivotColumn A B j ℓ :=
        (Finset.mem_filter.mp hℓs).2
      let Bfun : Fin m → Fin n := fun i => if i = ℓ then j else B i
      have hBfun : Function.Injective Bfun := by
        intro p q hpq
        by_cases hp : p = ℓ
        · subst p
          by_cases hq : q = ℓ
          · exact hq.symm
          · exfalso
            apply hj
            refine ⟨q, ?_⟩
            simpa [Bfun, hq] using hpq.symm
        · by_cases hq : q = ℓ
          · subst q
            exfalso
            apply hj
            refine ⟨p, ?_⟩
            simpa [Bfun, hp] using hpq
          · apply B.injective
            simpa [Bfun, hp, hq] using hpq
      let B' : Fin m ↪ Fin n := ⟨Bfun, hBfun⟩
      let x' : Fin n → ℝ := x +
        (x (B ℓ) / LinearOptimization.pivotColumn A B j ℓ) •
          LinearOptimization.basicDirection A B j
      apply False.elim
      apply hterminal
      refine ⟨B', x', ?_⟩
      refine ⟨j, ℓ, ?_, ?_⟩
      · refine ⟨hj, hcj, hℓ, ?_, ?_, rfl⟩
        · intro i hi
          simp [B', Bfun, hi]
        · simp [B', Bfun]
      · intro i hi
        exact hmin i (by simp [s, hi])
    · right
      push_neg at hpositive
      let d : Fin n → ℝ := LinearOptimization.basicDirection A B j
      have hdker : A.mulVec d = 0 := basicDirection_kernel A B j
      have hdnonneg : 0 ≤ d := by
        intro k
        by_cases hkB : k ∈ Set.range B
        · obtain ⟨i, rfl⟩ := hkB
          change (0 : ℝ) ≤ d (B i)
          dsimp [d]
          rw [basicDirection_basic A B j hj i]
          exact neg_nonneg.mpr (hpositive i)
        · by_cases hkj : k = j
          · subst k
            change (0 : ℝ) ≤ d j
            dsimp [d]
            rw [basicDirection_entering A B j hj]
            norm_num
          · change (0 : ℝ) ≤ d k
            dsimp [d]
            rw [basicDirection_other A B j k hkj hkB]
      have hdcost : c ⬝ᵥ d < 0 := by
        rw [dot_basicDirection_eq_reducedCost A c B j]
        exact hcj
      refine ⟨d, hdker, hdnonneg, hdcost, ?_⟩
      rw [LinearOptimization.lpValue, iInf_eq_bot]
      intro z hz
      induction z using EReal.rec with
      | bot => exact (lt_irrefl _ hz).elim
      | coe r =>
          let lam : ℝ := max 0
            ((c ⬝ᵥ x - r + 1) / (-(c ⬝ᵥ d)))
          have hden : 0 < -(c ⬝ᵥ d) := by linarith
          have hlam : 0 ≤ lam := le_max_left _ _
          have hge : (c ⬝ᵥ x - r + 1) / (-(c ⬝ᵥ d)) ≤ lam :=
            le_max_right _ _
          have hkey : c ⬝ᵥ x - r + 1 ≤ lam * (-(c ⬝ᵥ d)) := by
            calc
              c ⬝ᵥ x - r + 1 =
                  ((c ⬝ᵥ x - r + 1) / (-(c ⬝ᵥ d))) *
                    (-(c ⬝ᵥ d)) := by
                rw [div_mul_cancel₀ _ (ne_of_gt hden)]
              _ ≤ lam * (-(c ⬝ᵥ d)) :=
                mul_le_mul_of_nonneg_right hge (le_of_lt hden)
          have hfeas : x + lam • d ∈ LinearOptimization.stdPolyhedron A b := by
            constructor
            · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hdker,
                smul_zero, add_zero]
            · intro k
              change 0 ≤ x k + lam * d k
              exact add_nonneg (hx.2 k) (mul_nonneg hlam (hdnonneg k))
          refine ⟨x + lam • d, ?_⟩
          have hcost : c ⬝ᵥ (x + lam • d) < r := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            linarith
          simpa [hfeas] using EReal.coe_lt_coe_iff.mpr hcost
      | top =>
          refine ⟨x, ?_⟩
          simpa [hx] using EReal.coe_lt_top (c ⬝ᵥ x)
