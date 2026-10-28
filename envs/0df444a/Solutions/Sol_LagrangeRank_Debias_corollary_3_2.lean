-- Prove2me | solution 1 for LagrangeRank.Debias.corollary_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:22:48.076737+00:00
-- url     : https://prove2.me/submissions/4ef333cb-1679-48fb-bb1a-fc8626d873b6

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace Aux_LRDeb32
open LagrangeRank.Debias Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

lemma rs_nonneg (M : Matrix m n ℝ) : 0 ≤ rowSumNorm M := NNReal.coe_nonneg _

lemma rs_ge (M : Matrix m n ℝ) (i : m) : ∑ j, |M i j| ≤ rowSumNorm M := by
  unfold rowSumNorm
  have h : (∑ j, ‖M i j‖₊ : NNReal) ≤ (Finset.univ : Finset m).sup (fun i => ∑ j, ‖M i j‖₊) :=
    Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) = ∑ j, |M i j| := by
    push_cast; simp [Real.norm_eq_abs]
  rw [← h2]
  exact_mod_cast h

lemma rs_le (M : Matrix m n ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, ∑ j, |M i j| ≤ c) :
    rowSumNorm M ≤ c := by
  unfold rowSumNorm
  have : (Finset.univ : Finset m).sup (fun i => ∑ j, ‖M i j‖₊) ≤ ⟨c, hc⟩ := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.1
    show ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ c
    push_cast
    simpa [Real.norm_eq_abs] using h i
  exact_mod_cast this

lemma abs_le_l1 (v : n → ℝ) (j : n) : |v j| ≤ l1Norm v :=
  Finset.single_le_sum (f := fun i => |v i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

lemma l1_nonneg (v : n → ℝ) : 0 ≤ l1Norm v := Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma mulVec_bound (M : Matrix m n ℝ) (v : n → ℝ) (i : m) :
    |(M *ᵥ v) i| ≤ rowSumNorm M * l1Norm v := by
  calc |(M *ᵥ v) i| = |∑ j, M i j * v j| := rfl
    _ ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * l1Norm v := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le_l1 v j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * l1Norm v := by rw [Finset.sum_mul]
    _ ≤ rowSumNorm M * l1Norm v := mul_le_mul_of_nonneg_right (rs_ge M i) (l1_nonneg v)

lemma dot_bound (a b : n → ℝ) (B : ℝ) (hb : ∀ i, |b i| ≤ B) : |a ⬝ᵥ b| ≤ l1Norm a * B := by
  calc |a ⬝ᵥ b| = |∑ i, a i * b i| := rfl
    _ ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * B := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = l1Norm a * B := by rw [← Finset.sum_mul]; rfl

lemma rs_mul {k : Type*} [Fintype k] (P : Matrix m k ℝ) (Q : Matrix k n ℝ) :
    rowSumNorm (P * Q) ≤ rowSumNorm P * rowSumNorm Q := by
  apply rs_le _ _ (mul_nonneg (rs_nonneg P) (rs_nonneg Q))
  intro i
  calc ∑ j, |(P * Q) i j| = ∑ j, |∑ l, P i l * Q l j| := rfl
    _ ≤ ∑ j, ∑ l, |P i l| * |Q l j| := by
        apply Finset.sum_le_sum; intro j _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro l _; rw [abs_mul]
    _ = ∑ l, |P i l| * ∑ j, |Q l j| := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro l _; rw [Finset.mul_sum]
    _ ≤ ∑ l, |P i l| * rowSumNorm Q := by
        apply Finset.sum_le_sum; intro l _
        exact mul_le_mul_of_nonneg_left (rs_ge Q l) (abs_nonneg _)
    _ = (∑ l, |P i l|) * rowSumNorm Q := by rw [Finset.sum_mul]
    _ ≤ rowSumNorm P * rowSumNorm Q := mul_le_mul_of_nonneg_right (rs_ge P i) (rs_nonneg Q)

lemma rs_tri (A B : Matrix m n ℝ) : rowSumNorm A ≤ rowSumNorm B + rowSumNorm (A - B) := by
  apply rs_le _ _ (add_nonneg (rs_nonneg B) (rs_nonneg _))
  intro i
  calc ∑ j, |A i j| ≤ ∑ j, (|B i j| + |(A - B) i j|) := by
        apply Finset.sum_le_sum; intro j _
        have : A i j = B i j + (A - B) i j := by simp
        rw [this]; exact abs_add_le _ _
    _ = ∑ j, |B i j| + ∑ j, |(A - B) i j| := Finset.sum_add_distrib
    _ ≤ rowSumNorm B + rowSumNorm (A - B) := add_le_add (rs_ge B i) (rs_ge _ i)

lemma l1_tri (a b : n → ℝ) : l1Norm a ≤ l1Norm b + l1Norm (a - b) := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  have : a j = b j + (a - b) j := by simp
  rw [this]
  simpa using abs_add_le (b j) ((a - b) j)


lemma s_bound {d : ℕ} (Ω Ωs : Matrix (Fin d) (Fin d) ℝ) (g gs : Fin d → ℝ)
    (A B L2 ρ1 ρ4 : ℝ) (h1 : 0 ≤ ρ1) (h4 : 0 ≤ ρ4) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hl1g : l1Norm g ≤ A) (hl1gs : l1Norm gs ≤ A) (hl1e : l1Norm (g - gs) ≤ |L2| * ρ1)
    (hrsΩs : rowSumNorm Ωs ≤ B) (hΩ : rowSumNorm (Ω - Ωs) ≤ ρ4) :
    |g ⬝ᵥ (Ω *ᵥ g) - gs ⬝ᵥ (Ωs *ᵥ gs)| ≤ ρ4 * (A * A) + ρ1 * (2 * A * B * |L2|) := by
  have key : g ⬝ᵥ (Ω *ᵥ g) - gs ⬝ᵥ (Ωs *ᵥ gs) = g ⬝ᵥ ((Ω - Ωs) *ᵥ g) + (g - gs) ⬝ᵥ (Ωs *ᵥ g) +
      gs ⬝ᵥ (Ωs *ᵥ (g - gs)) := by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    ring
  have hL0 := abs_nonneg L2
  have t1 : |g ⬝ᵥ ((Ω - Ωs) *ᵥ g)| ≤ A * (ρ4 * A) := by
    refine (dot_bound g _ _ (fun i => mulVec_bound (Ω - Ωs) g i)).trans ?_
    exact mul_le_mul hl1g (mul_le_mul hΩ hl1g (l1_nonneg _) h4) (mul_nonneg (rs_nonneg _)
      (l1_nonneg _)) hA0
  have t2 : |(g - gs) ⬝ᵥ (Ωs *ᵥ g)| ≤ (|L2| * ρ1) * (B * A) := by
    refine (dot_bound _ _ _ (fun i => mulVec_bound Ωs g i)).trans ?_
    exact mul_le_mul hl1e (mul_le_mul hrsΩs hl1g (l1_nonneg _) hB0)
      (mul_nonneg (rs_nonneg _) (l1_nonneg _)) (mul_nonneg hL0 h1)
  have t3 : |gs ⬝ᵥ (Ωs *ᵥ (g - gs))| ≤ A * (B * (|L2| * ρ1)) := by
    refine (dot_bound _ _ _ (fun i => mulVec_bound Ωs (g - gs) i)).trans ?_
    exact mul_le_mul hl1gs (mul_le_mul hrsΩs hl1e (l1_nonneg _) hB0)
      (mul_nonneg (rs_nonneg _) (l1_nonneg _)) hA0
  rw [key]
  have a1 := abs_add_le (g ⬝ᵥ ((Ω - Ωs) *ᵥ g) + (g - gs) ⬝ᵥ (Ωs *ᵥ g)) (gs ⬝ᵥ (Ωs *ᵥ (g - gs)))
  have a2 := abs_add_le (g ⬝ᵥ ((Ω - Ωs) *ᵥ g)) ((g - gs) ⬝ᵥ (Ωs *ᵥ g))
  have e : ρ4 * (A * A) + ρ1 * (2 * A * B * |L2|) =
      A * (ρ4 * A) + (|L2| * ρ1) * (B * A) + A * (B * (|L2| * ρ1)) := by ring
  rw [e]
  linarith only [a1, a2, t1, t2, t3]

lemma tb11 {p q : Type*} [DecidableEq p] [DecidableEq q] (P : Matrix p p ℝ) (Q : Matrix p q ℝ)
    (R : Matrix q p ℝ) (S : Matrix q q ℝ) :
    (1 - fromBlocks P Q R S).toBlocks₁₁ = 1 - P := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

lemma tb12 {p q : Type*} [DecidableEq p] [DecidableEq q] (P : Matrix p p ℝ) (Q : Matrix p q ℝ)
    (R : Matrix q p ℝ) (S : Matrix q q ℝ) :
    (1 - fromBlocks P Q R S).toBlocks₁₂ = 0 - Q := by
  ext i j; simp [Matrix.toBlocks₁₂, Matrix.one_apply]

lemma tb22 {p q : Type*} [DecidableEq p] [DecidableEq q] (P : Matrix p p ℝ) (Q : Matrix p q ℝ)
    (R : Matrix q p ℝ) (S : Matrix q q ℝ) :
    (1 - fromBlocks P Q R S).toBlocks₂₂ = 1 - S := by
  ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]

lemma blocks {d : ℕ} (Ω H : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ)
    (hsne : g ⬝ᵥ (Ω *ᵥ g) ≠ 0) :
    (1 - thetaBlock Ω g * borderedHessian H g).toBlocks₁₁ =
        (1 - (g ⬝ᵥ (Ω *ᵥ g))⁻¹ • vecMulVec (Ω *ᵥ g) g) * (1 - Ω * H) ∧
      (1 - thetaBlock Ω g * borderedHessian H g).toBlocks₁₂ = 0 ∧
      (1 - thetaBlock Ω g * borderedHessian H g).toBlocks₂₂ = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, u = Ω *ᵥ g := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = g ⬝ᵥ (Ω *ᵥ g) := ⟨_, rfl⟩
  rw [← hu] at hs hsne ⊢
  rw [← hs] at hsne ⊢
  have hT : thetaBlock Ω g = fromBlocks (Ω - s⁻¹ • vecMulVec u (g ᵥ* Ω))
      (replicateCol Unit (s⁻¹ • u)) (replicateRow Unit (s⁻¹ • u))
      (Matrix.of fun _ _ => -s⁻¹) := by
    rw [hs, hu]; rfl
  have hBH : borderedHessian H g =
      fromBlocks H (replicateCol Unit g) (replicateRow Unit g) 0 := rfl
  rw [hT, hBH]
  first | rw [fromBlocks_multiply] | simp only [fromBlocks_multiply]
  rw [tb11, tb12, tb22]
  refine ⟨?_, ?_, ?_⟩
  · have e1 : replicateCol Unit (s⁻¹ • u) * replicateRow Unit g = s⁻¹ • vecMulVec u g := by
      rw [← vecMulVec_eq Unit]
      ext i j
      simp [vecMulVec_apply, mul_assoc]
    have e2 : vecMulVec u (g ᵥ* Ω) = vecMulVec u g * Ω := (vecMulVec_mul u g Ω).symm
    rw [e1, e2]
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
      Matrix.mul_assoc]
    abel
  · rw [Matrix.mul_zero, add_zero, ← replicateCol_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, vecMulVec_mulVec, ← Matrix.dotProduct_mulVec]
    have : (MulOpposite.op (g ⬝ᵥ (Ω *ᵥ g)) • u : Fin d → ℝ) = s • u := by
      ext i; simp [hs, hu, mul_comm]
    rw [this, smul_smul, inv_mul_cancel₀ hsne, one_smul, hu, sub_self, replicateCol_zero,
      sub_zero]
  · rw [Matrix.mul_zero, add_zero, replicateRow_mul_replicateCol]
    ext i j
    have : (s⁻¹ • u) ⬝ᵥ g = 1 := by
      rw [smul_dotProduct, dotProduct_comm, ← hs, smul_eq_mul, inv_mul_cancel₀ hsne]
    simp [this]

lemma P_bound {d : ℕ} (Ω : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) (A B K : ℝ)
    (hs0 : 0 < g ⬝ᵥ (Ω *ᵥ g)) (hsinv : (g ⬝ᵥ (Ω *ᵥ g))⁻¹ ≤ K) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hK0 : 0 ≤ K) (hl1g : l1Norm g ≤ A) (hrsΩ : rowSumNorm Ω ≤ B) :
    rowSumNorm (1 - (g ⬝ᵥ (Ω *ᵥ g))⁻¹ • vecMulVec (Ω *ᵥ g) g) ≤ 1 + K * (B * A) * A := by
  obtain ⟨u, hu⟩ : ∃ u, u = Ω *ᵥ g := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = g ⬝ᵥ (Ω *ᵥ g) := ⟨_, rfl⟩
  rw [← hu] at hs hs0 hsinv ⊢
  rw [← hs] at hs0 hsinv ⊢
  apply rs_le _ _ (by positivity)
  intro i
  have hui : |u i| ≤ B * A := hu ▸ (mulVec_bound Ω g i).trans
    (mul_le_mul hrsΩ hl1g (l1_nonneg _) hB0)
  calc ∑ j, |(1 - s⁻¹ • vecMulVec u g) i j|
      ≤ ∑ j, (|(1 : Matrix (Fin d) (Fin d) ℝ) i j| + s⁻¹ * |u i| * |g j|) := by
        apply Finset.sum_le_sum; intro j _
        simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hs0), mul_assoc]
    _ = 1 + s⁻¹ * |u i| * l1Norm g := by
        have hone : ∀ x, |(1 : Matrix (Fin d) (Fin d) ℝ) i x| = if i = x then 1 else 0 := by
          intro x; by_cases h : i = x <;> simp [Matrix.one_apply, h]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_congr rfl (fun x _ => hone x),
          Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        rfl
    _ ≤ 1 + K * (B * A) * A := by
        have : s⁻¹ * |u i| * l1Norm g ≤ K * (B * A) * A :=
          mul_le_mul (mul_le_mul hsinv hui (abs_nonneg _) hK0) hl1g
            (l1_nonneg _) (by positivity)
        linarith only [this]

end Aux_LRDeb32

open LagrangeRank.Debias Matrix Aux_LRDeb32 in
theorem solution (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (OmHat OmStar H : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
        (ρ1 ρ3 ρ4 : ℝ),
        0 ≤ ρ1 → 0 ≤ ρ3 → 0 ≤ ρ4 → ρ1 + ρ4 ≤ δ →
        l1Norm gStar ≤ c1 → l1Norm (gHat - gStar) ≤ L2 * ρ1 →
        rowSumNorm OmStar ≤ c2 → c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm (1 - OmHat * H) ≤ ρ3 →
        rowSumNorm (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₁₁
            ≤ C * ρ3 ∧
        (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₁₂ = 0 ∧
        (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₂₂ = 0 := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |c1| + |L2| + 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |c2| + 1 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = A * A + 2 * A * B * |L2| := ⟨_, rfl⟩
  have hc1 := le_abs_self c1
  have hc2 := le_abs_self c2
  have hL0 := abs_nonneg L2
  have hL2' := le_abs_self L2
  have hA1 : 1 ≤ A := by have := abs_nonneg c1; linarith only [hA, this, hL0]
  have hB1 : 1 ≤ B := by have := abs_nonneg c2; linarith only [hB, this]
  have hA0 : 0 ≤ A := by linarith only [hA1]
  have hB0 : 0 ≤ B := by linarith only [hB1]
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨1 + 2 / c3 * (B * A) * A, min 1 (c3 / (2 * (M + 1))), by positivity,
    lt_min one_pos (by positivity), ?_⟩
  intro d Ω Ωs H g gs ρ1 ρ3 ρ4 h1 h3 h4 hδ hgs hg hΩs hc3' hΩ hQ
  have hδ1 : ρ1 + ρ4 ≤ 1 := hδ.trans (min_le_left _ _)
  have hδ2 : ρ1 + ρ4 ≤ c3 / (2 * (M + 1)) := hδ.trans (min_le_right _ _)
  have hL2 : L2 * ρ1 ≤ |L2| * ρ1 := mul_le_mul_of_nonneg_right hL2' h1
  have hl1e : l1Norm (g - gs) ≤ |L2| * ρ1 := hg.trans hL2
  have hLρ : |L2| * ρ1 ≤ |L2| := by
    have : ρ1 ≤ 1 := by linarith only [hδ1, h4]
    calc |L2| * ρ1 ≤ |L2| * 1 := mul_le_mul_of_nonneg_left this hL0
      _ = |L2| := mul_one _
  have hl1g : l1Norm g ≤ A := by
    have := l1_tri g gs
    linarith only [this, hl1e, hLρ, hgs, hc1, hA]
  have hl1gs : l1Norm gs ≤ A := by linarith only [hgs, hc1, hA, hL0]
  have hrsΩs : rowSumNorm Ωs ≤ B := by linarith only [hΩs, hc2, hB]
  have hrsΩ : rowSumNorm Ω ≤ B := by
    have := rs_tri Ω Ωs
    linarith only [this, hΩs, hΩ, hδ1, h1, hc2, hB]
  have hdiff := s_bound Ω Ωs g gs A B L2 ρ1 ρ4 h1 h4 hA0 hB0 hl1g hl1gs hl1e hrsΩs hΩ
  have hdiff' : |g ⬝ᵥ (Ω *ᵥ g) - gs ⬝ᵥ (Ωs *ᵥ gs)| ≤ (ρ1 + ρ4) * M := by
    have e : (ρ1 + ρ4) * M = ρ4 * (A * A) + ρ1 * (2 * A * B * |L2|) +
        (ρ1 * (A * A) + ρ4 * (2 * A * B * |L2|)) := by rw [hM]; ring
    have : 0 ≤ ρ1 * (A * A) + ρ4 * (2 * A * B * |L2|) := by positivity
    rw [e]; linarith only [hdiff, this]
  have hsmall : (ρ1 + ρ4) * M < c3 / 2 := by
    have h5 : (ρ1 + ρ4) * M ≤ c3 / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hδ2 hM0
    have h6 : c3 / (2 * (M + 1)) * M < c3 / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have : c3 / 2 * (2 * (M + 1)) = c3 * M + c3 := by ring
      rw [this]; linarith only [hc3]
    linarith only [h5, h6]
  have hspos : c3 / 2 ≤ g ⬝ᵥ (Ω *ᵥ g) := by
    have := (abs_le.1 hdiff').1
    linarith only [this, hsmall, hc3']
  have hs0 : 0 < g ⬝ᵥ (Ω *ᵥ g) := by linarith only [hspos, hc3]
  have hsinv : (g ⬝ᵥ (Ω *ᵥ g))⁻¹ ≤ 2 / c3 := by
    rw [inv_le_comm₀ hs0 (by positivity), inv_div]
    exact hspos
  obtain ⟨b11, b12, b22⟩ := blocks Ω H g hs0.ne'
  refine ⟨?_, b12, b22⟩
  rw [b11]
  have hP := P_bound Ω g A B (2 / c3) hs0 hsinv hA0 hB0 (by positivity) hl1g hrsΩ
  calc rowSumNorm ((1 - (g ⬝ᵥ (Ω *ᵥ g))⁻¹ • vecMulVec (Ω *ᵥ g) g) * (1 - Ω * H))
      ≤ rowSumNorm (1 - (g ⬝ᵥ (Ω *ᵥ g))⁻¹ • vecMulVec (Ω *ᵥ g) g) * rowSumNorm (1 - Ω * H) :=
        rs_mul _ _
    _ ≤ (1 + 2 / c3 * (B * A) * A) * ρ3 :=
        mul_le_mul hP hQ (rs_nonneg _) (by positivity)
