-- Prove2me | solution 1 for LagrangeRank.Debias.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:31:04.859852+00:00
-- url     : https://prove2.me/submissions/2e4d89f7-e2b4-4261-96eb-44e877ce39ae

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix

section norms
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma rowSumNorm_nonneg (M : Matrix m n ℝ) : 0 ≤ rowSumNorm M := by
  unfold rowSumNorm; exact NNReal.coe_nonneg _

lemma rowSum_le_rowSumNorm (M : Matrix m n ℝ) (i : m) : ∑ j, |M i j| ≤ rowSumNorm M := by
  unfold rowSumNorm
  have : (∑ j, ‖M i j‖₊ : NNReal) ≤
      (Finset.univ : Finset m).sup fun i => (∑ j, ‖M i j‖₊ : NNReal) :=
    Finset.le_sup (f := fun i => (∑ j, ‖M i j‖₊ : NNReal)) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [NNReal.coe_sum] using h2

lemma rowSumNorm_le {M : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, |M i j| ≤ c) :
    rowSumNorm M ≤ c := by
  unfold rowSumNorm
  have : ((Finset.univ : Finset m).sup fun i => (∑ j, ‖M i j‖₊ : NNReal)) ≤ c.toNNReal := by
    apply Finset.sup_le; intro i _
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc]
    simpa [NNReal.coe_sum] using h i
  calc _ ≤ ((c.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 this
    _ = c := Real.coe_toNNReal _ hc

lemma l1Norm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ l1Norm v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma norm_le_l1Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ‖v‖ ≤ l1Norm v := by
  rw [pi_norm_le_iff_of_nonneg (l1Norm_nonneg v)]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma abs_le_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

lemma l1Norm_add_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    l1Norm (u + v) ≤ l1Norm u + l1Norm v := by
  unfold l1Norm; rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)

lemma l1Norm_sub_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    l1Norm (u - v) ≤ l1Norm u + l1Norm v := by
  unfold l1Norm; rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_sub _ _)

lemma l1Norm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    l1Norm (c • v) = |c| * l1Norm v := by
  unfold l1Norm; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [abs_mul])

lemma l1Norm_neg {ι : Type*} [Fintype ι] (v : ι → ℝ) : l1Norm (-v) = l1Norm v := by
  unfold l1Norm; simp

lemma mulVec_norm_le (M : Matrix m n ℝ) (v : n → ℝ) : ‖M *ᵥ v‖ ≤ rowSumNorm M * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (rowSumNorm_nonneg M) (norm_nonneg v))]
  intro i
  rw [Real.norm_eq_abs, mulVec, dotProduct]
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖v‖ := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_norm v j) (abs_nonneg _))
    _ = (∑ j, |M i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ rowSumNorm M * ‖v‖ :=
        mul_le_mul_of_nonneg_right (rowSum_le_rowSumNorm M i) (norm_nonneg v)

lemma rowSumNorm_mul_le (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    rowSumNorm (A * B) ≤ rowSumNorm A * rowSumNorm B := by
  apply rowSumNorm_le (mul_nonneg (rowSumNorm_nonneg A) (rowSumNorm_nonneg B))
  intro i
  calc ∑ j, |(A * B) i j| = ∑ j, |∑ k, A i k * B k j| := by simp [Matrix.mul_apply]
    _ ≤ ∑ j, ∑ k, |A i k| * |B k j| := Finset.sum_le_sum (fun j _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (by simp [abs_mul]))
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    _ ≤ ∑ k, |A i k| * rowSumNorm B := Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (rowSum_le_rowSumNorm B k) (abs_nonneg _))
    _ = (∑ k, |A i k|) * rowSumNorm B := by rw [Finset.sum_mul]
    _ ≤ rowSumNorm A * rowSumNorm B :=
        mul_le_mul_of_nonneg_right (rowSum_le_rowSumNorm A i) (rowSumNorm_nonneg B)

lemma rowSumNorm_add_le (A B : Matrix m n ℝ) :
    rowSumNorm (A + B) ≤ rowSumNorm A + rowSumNorm B := by
  apply rowSumNorm_le (add_nonneg (rowSumNorm_nonneg A) (rowSumNorm_nonneg B))
  intro i
  calc ∑ j, |(A + B) i j| ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun j _ => by simpa using abs_add_le (A i j) (B i j))
    _ = ∑ j, |A i j| + ∑ j, |B i j| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (rowSum_le_rowSumNorm A i) (rowSum_le_rowSumNorm B i)

lemma rowSumNorm_sub_le (A B : Matrix m n ℝ) :
    rowSumNorm (A - B) ≤ rowSumNorm A + rowSumNorm B := by
  apply rowSumNorm_le (add_nonneg (rowSumNorm_nonneg A) (rowSumNorm_nonneg B))
  intro i
  calc ∑ j, |(A - B) i j| ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun j _ => by simpa using abs_sub (A i j) (B i j))
    _ = ∑ j, |A i j| + ∑ j, |B i j| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (rowSum_le_rowSumNorm A i) (rowSum_le_rowSumNorm B i)

lemma rowSumNorm_smul_le (c : ℝ) (A : Matrix m n ℝ) :
    rowSumNorm (c • A) ≤ |c| * rowSumNorm A := by
  apply rowSumNorm_le (mul_nonneg (abs_nonneg _) (rowSumNorm_nonneg A))
  intro i
  calc ∑ j, |(c • A) i j| = |c| * ∑ j, |A i j| := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by simp [abs_mul])
    _ ≤ _ := mul_le_mul_of_nonneg_left (rowSum_le_rowSumNorm A i) (abs_nonneg _)

lemma rowSumNorm_vecMulVec_le (a : m → ℝ) (b : n → ℝ) :
    rowSumNorm (vecMulVec a b) ≤ ‖a‖ * l1Norm b := by
  apply rowSumNorm_le (mul_nonneg (norm_nonneg _) (l1Norm_nonneg _))
  intro i
  calc ∑ j, |vecMulVec a b i j| = |a i| * l1Norm b := by
        unfold l1Norm; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by simp [vecMulVec_apply, abs_mul])
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_le_norm a i) (l1Norm_nonneg _)

lemma abs_dotProduct_le (u w : n → ℝ) : |u ⬝ᵥ w| ≤ l1Norm u * ‖w‖ := by
  unfold dotProduct l1Norm
  calc |∑ i, u i * w i| ≤ ∑ i, |u i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |u i| * ‖w‖ := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_norm w i) (abs_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

lemma l1Norm_vecMul_le (v : m → ℝ) (M : Matrix m n ℝ) :
    l1Norm (v ᵥ* M) ≤ l1Norm v * rowSumNorm M := by
  unfold l1Norm
  calc ∑ j, |(v ᵥ* M) j| = ∑ j, |∑ i, v i * M i j| := by simp [vecMul, dotProduct]
    _ ≤ ∑ j, ∑ i, |v i| * |M i j| := Finset.sum_le_sum (fun j _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (by simp [abs_mul]))
    _ = ∑ i, |v i| * ∑ j, |M i j| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    _ ≤ ∑ i, |v i| * rowSumNorm M := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (rowSum_le_rowSumNorm M i) (abs_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

end norms

section theta

variable {d : ℕ}

lemma thetaBlock_eq (O : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    thetaBlock O g =
      fromBlocks (O - (g ⬝ᵥ (O *ᵥ g))⁻¹ • vecMulVec (O *ᵥ g) (g ᵥ* O))
        (replicateCol Unit ((g ⬝ᵥ (O *ᵥ g))⁻¹ • (O *ᵥ g)))
        (replicateRow Unit ((g ⬝ᵥ (O *ᵥ g))⁻¹ • (O *ᵥ g)))
        (Matrix.of fun _ _ => -(g ⬝ᵥ (O *ᵥ g))⁻¹) := rfl

lemma thetaBlock_11 (O : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (thetaBlock O g).toBlocks₁₁ =
      O - (g ⬝ᵥ (O *ᵥ g))⁻¹ • vecMulVec (O *ᵥ g) (g ᵥ* O) := by
  rw [thetaBlock_eq]; exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

lemma thetaBlock_12 (O : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) (k : Fin d) :
    (thetaBlock O g).toBlocks₁₂ k () = (g ⬝ᵥ (O *ᵥ g))⁻¹ * (O *ᵥ g) k := by
  rw [thetaBlock_eq, Matrix.toBlocks_fromBlocks₁₂]; simp [replicateCol]

lemma thetaBlock_22 (O : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (thetaBlock O g).toBlocks₂₂ () () = -(g ⬝ᵥ (O *ᵥ g))⁻¹ := by
  rw [thetaBlock_eq, Matrix.toBlocks_fromBlocks₂₂]; simp

/-- Hypotheses of Corollary 3.1 (with nonnegative constants). -/
structure Cond (c1 c2 L : ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
    (ρ1 ρ4 : ℝ) : Prop where
  ρ1_nn : 0 ≤ ρ1
  ρ4_nn : 0 ≤ ρ4
  g1 : l1Norm gStar ≤ c1
  gd : l1Norm (gHat - gStar) ≤ L * ρ1
  O2 : rowSumNorm OmStar ≤ c2
  Od : rowSumNorm (OmHat - OmStar) ≤ ρ4

variable {c1 c2 L : ℝ} {OmHat OmStar : Matrix (Fin d) (Fin d) ℝ} {gHat gStar : Fin d → ℝ}
  {ρ1 ρ4 : ℝ}

lemma Cond.l1_hat (h : Cond c1 c2 L OmHat OmStar gHat gStar ρ1 ρ4) (hL : 0 ≤ L)
    (ha : ρ1 + ρ4 ≤ 1) : l1Norm gHat ≤ c1 + L := by
  have h1 : gHat = (gHat - gStar) + gStar := by abel
  have h2 := l1Norm_add_le (gHat - gStar) gStar
  rw [← h1] at h2
  have h3 : L * ρ1 ≤ L := by nlinarith [h.ρ1_nn, h.ρ4_nn]
  linarith [h.g1, h.gd]

lemma Cond.rs_hat (h : Cond c1 c2 L OmHat OmStar gHat gStar ρ1 ρ4)
    (ha : ρ1 + ρ4 ≤ 1) : rowSumNorm OmHat ≤ c2 + 1 := by
  have h1 : OmHat = (OmHat - OmStar) + OmStar := by abel
  have h2 := rowSumNorm_add_le (OmHat - OmStar) OmStar
  rw [← h1] at h2
  linarith [h.O2, h.Od, h.ρ1_nn]

def Dc (c1 c2 L : ℝ) : ℝ := L * (c2 + 1) * (c1 + L) + c1 * (c1 + L) + c1 * c2 * L

lemma Cond.s_diff (h : Cond c1 c2 L OmHat OmStar gHat gStar ρ1 ρ4)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hL : 0 ≤ L) (ha : ρ1 + ρ4 ≤ 1) :
    |(gHat ⬝ᵥ (OmHat *ᵥ gHat)) - (gStar ⬝ᵥ (OmStar *ᵥ gStar))|
      ≤ Dc c1 c2 L * (ρ1 + ρ4) := by
  unfold Dc
  have hg := h.l1_hat hL ha
  have hO := h.rs_hat ha
  have hr1 := h.ρ1_nn
  have hr4 := h.ρ4_nn
  have e : (gHat ⬝ᵥ (OmHat *ᵥ gHat)) - (gStar ⬝ᵥ (OmStar *ᵥ gStar)) =
      (gHat - gStar) ⬝ᵥ (OmHat *ᵥ gHat) + gStar ⬝ᵥ ((OmHat - OmStar) *ᵥ gHat)
        + gStar ⬝ᵥ (OmStar *ᵥ (gHat - gStar)) := by
    simp only [sub_dotProduct, sub_mulVec, dotProduct_sub, mulVec_sub]; ring
  have t1 : |(gHat - gStar) ⬝ᵥ (OmHat *ᵥ gHat)| ≤ L * ρ1 * ((c2 + 1) * (c1 + L)) := by
    refine (abs_dotProduct_le _ _).trans ?_
    refine mul_le_mul h.gd ?_ (norm_nonneg _) (mul_nonneg hL hr1)
    exact (mulVec_norm_le _ _).trans (mul_le_mul hO ((norm_le_l1Norm _).trans hg)
      (norm_nonneg _) (by linarith))
  have t2 : |gStar ⬝ᵥ ((OmHat - OmStar) *ᵥ gHat)| ≤ c1 * (ρ4 * (c1 + L)) := by
    refine (abs_dotProduct_le _ _).trans ?_
    refine mul_le_mul h.g1 ?_ (norm_nonneg _) hc1
    exact (mulVec_norm_le _ _).trans (mul_le_mul h.Od ((norm_le_l1Norm _).trans hg)
      (norm_nonneg _) hr4)
  have t3 : |gStar ⬝ᵥ (OmStar *ᵥ (gHat - gStar))| ≤ c1 * (c2 * (L * ρ1)) := by
    refine (abs_dotProduct_le _ _).trans ?_
    refine mul_le_mul h.g1 ?_ (norm_nonneg _) hc1
    exact (mulVec_norm_le _ _).trans (mul_le_mul h.O2 ((norm_le_l1Norm _).trans h.gd)
      (norm_nonneg _) hc2)
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  have : L * ρ1 * ((c2 + 1) * (c1 + L)) + c1 * (ρ4 * (c1 + L)) + c1 * (c2 * (L * ρ1)) ≤
      (L * (c2 + 1) * (c1 + L) + c1 * (c1 + L) + c1 * c2 * L) * (ρ1 + ρ4) := by
    have a1 : 0 ≤ L * (c2 + 1) * (c1 + L) := by positivity
    have a2 : 0 ≤ c1 * (c1 + L) := by positivity
    have a3 : 0 ≤ c1 * c2 * L := by positivity
    nlinarith [mul_nonneg a1 hr4, mul_nonneg a2 hr1, mul_nonneg a3 hr4]
  linarith

end theta

section cor

lemma toBlocks₁₁_sub {d : ℕ} (A B : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) :
    (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by
  ext i j; simp [Matrix.toBlocks₁₁]

lemma toBlocks₁₂_sub {d : ℕ} (A B : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (k : Fin d) :
    (A - B).toBlocks₁₂ k () = A.toBlocks₁₂ k () - B.toBlocks₁₂ k () := by
  simp [Matrix.toBlocks₁₂]

lemma toBlocks₂₂_sub {d : ℕ} (A B : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) :
    (A - B).toBlocks₂₂ () () = A.toBlocks₂₂ () () - B.toBlocks₂₂ () () := by
  simp [Matrix.toBlocks₂₂]

lemma toBlocks₂₁_sub {d : ℕ} (A B : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (k : Fin d) :
    (A - B).toBlocks₂₁ () k = A.toBlocks₂₁ () k - B.toBlocks₂₁ () k := by
  simp [Matrix.toBlocks₂₁]

/-- Lower bound for the estimated scalar `ŝ`. -/
lemma s_lower (c1 c2 c3 L : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hL : 0 ≤ L) (hc3 : 0 < c3) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (d : ℕ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ) (ρ1 ρ4 : ℝ),
        Cond c1 c2 L OmHat OmStar gHat gStar ρ1 ρ4 → ρ1 + ρ4 ≤ δ →
        c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) → c3 / 2 ≤ gHat ⬝ᵥ (OmHat *ᵥ gHat) := by
  have hD : 0 ≤ Dc c1 c2 L := by unfold Dc; positivity
  refine ⟨min 1 (c3 / (2 * (Dc c1 c2 L + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro d OmHat OmStar gHat gStar ρ1 ρ4 h ha hs
  have ha1 : ρ1 + ρ4 ≤ 1 := ha.trans (min_le_left _ _)
  have hsd := h.s_diff hc1 hc2 hL ha1
  have hDa : Dc c1 c2 L * (ρ1 + ρ4) ≤ c3 / 2 := by
    calc Dc c1 c2 L * (ρ1 + ρ4) ≤ Dc c1 c2 L * (c3 / (2 * (Dc c1 c2 L + 1))) :=
          mul_le_mul_of_nonneg_left (ha.trans (min_le_right _ _)) hD
      _ = c3 / 2 * (Dc c1 c2 L / (Dc c1 c2 L + 1)) := by field_simp
      _ ≤ c3 / 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = c3 / 2 := mul_one _
  have := (abs_le.1 hsd).1
  linarith

theorem cor_aux (c1 c2 c3 L : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hL : 0 ≤ L) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (d : ℕ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ) (ρ1 ρ4 : ℝ),
        Cond c1 c2 L OmHat OmStar gHat gStar ρ1 ρ4 → ρ1 + ρ4 ≤ δ →
        c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        |(thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₂₂ () ()| ≤ C * (ρ1 + ρ4) ∧
        ‖fun k => (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₂ k ()‖
          ≤ C * (ρ1 + ρ4) ∧
        rowSumNorm (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₁
          ≤ C * (ρ1 + ρ4) := by
  have hD : 0 ≤ Dc c1 c2 L := by unfold Dc; positivity
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := s_lower c1 c2 c3 L hc1 hc2 hL hc3
  set D := Dc c1 c2 L with hDdef
  set Mu := (c2 + 1) * (c1 + L) with hMu
  set E := (c1 + L) + c2 * L with hE
  set F := L * (c2 + 1) + c1 with hF
  set Kt := 2 * D / c3 ^ 2 with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  have hMu0 : 0 ≤ Mu := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hF0 : 0 ≤ F := by positivity
  set C12 := Kt * Mu + E / c3 with hC12
  set C11 := 1 + Kt * Mu * Mu + E * Mu / c3 + c2 * c1 * F / c3 with hC11
  have hC12' : 0 ≤ C12 := by positivity
  have hC11' : 0 ≤ C11 := by positivity
  refine ⟨1 + Kt + C12 + C11, δ, by positivity, hδ0, hδ1, ?_⟩
  intro d OmHat OmStar gHat gStar ρ1 ρ4 h ha hs
  have hr1 := h.ρ1_nn
  have hr4 := h.ρ4_nn
  have ha1 : ρ1 + ρ4 ≤ 1 := ha.trans hδ1
  have ha0 : 0 ≤ ρ1 + ρ4 := add_nonneg hr1 hr4
  have hshat := hδ d OmHat OmStar gHat gStar ρ1 ρ4 h ha hs
  have hsd := h.s_diff hc1 hc2 hL ha1
  set sh := gHat ⬝ᵥ (OmHat *ᵥ gHat) with hsh
  set ss := gStar ⬝ᵥ (OmStar *ᵥ gStar) with hss
  have hsh0 : 0 < sh := by linarith
  have hss0 : 0 < ss := by linarith
  -- difference of inverses
  have ht : |sh⁻¹ - ss⁻¹| ≤ Kt * (ρ1 + ρ4) := by
    rw [inv_sub_inv hsh0.ne' hss0.ne', abs_div, abs_mul, abs_of_pos hsh0, abs_of_pos hss0]
    have h1 : |sh - ss| ≤ D * (ρ1 + ρ4) := hsd
    calc |ss - sh| / (sh * ss) ≤ D * (ρ1 + ρ4) / (c3 / 2 * c3) := by
          rw [abs_sub_comm]
          apply div_le_div₀ (by positivity) h1 (by positivity)
          exact mul_le_mul hshat hs hc3.le (by positivity)
      _ = Kt * (ρ1 + ρ4) := by rw [hKt]; field_simp
  have hts : ss⁻¹ ≤ 1 / c3 := by
    rw [one_div]; exact inv_anti₀ hc3 hs
  have hts0 : 0 ≤ ss⁻¹ := inv_nonneg.2 hss0.le
  -- vector bounds
  have hg := h.l1_hat hL ha1
  have hO := h.rs_hat ha1
  have hgn : ‖gHat‖ ≤ c1 + L := (norm_le_l1Norm _).trans hg
  have hu : ‖OmHat *ᵥ gHat‖ ≤ Mu :=
    (mulVec_norm_le _ _).trans (mul_le_mul hO hgn (norm_nonneg _) (by positivity))
  have hv : l1Norm (gHat ᵥ* OmHat) ≤ Mu := by
    refine (l1Norm_vecMul_le _ _).trans ?_
    rw [hMu, mul_comm (c2 + 1)]
    exact mul_le_mul hg hO (rowSumNorm_nonneg _) (by positivity)
  have hus : ‖OmStar *ᵥ gStar‖ ≤ c2 * c1 :=
    (mulVec_norm_le _ _).trans (mul_le_mul h.O2 ((norm_le_l1Norm _).trans h.g1)
      (norm_nonneg _) hc2)
  have hgd : ‖gHat - gStar‖ ≤ L * ρ1 := (norm_le_l1Norm _).trans h.gd
  have huu : ‖OmHat *ᵥ gHat - OmStar *ᵥ gStar‖ ≤ E * (ρ1 + ρ4) := by
    have e : OmHat *ᵥ gHat - OmStar *ᵥ gStar =
        (OmHat - OmStar) *ᵥ gHat + OmStar *ᵥ (gHat - gStar) := by
      rw [sub_mulVec, mulVec_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(OmHat - OmStar) *ᵥ gHat‖ ≤ ρ4 * (c1 + L) :=
      (mulVec_norm_le _ _).trans (mul_le_mul h.Od hgn (norm_nonneg _) hr4)
    have t2 : ‖OmStar *ᵥ (gHat - gStar)‖ ≤ c2 * (L * ρ1) :=
      (mulVec_norm_le _ _).trans (mul_le_mul h.O2 hgd (norm_nonneg _) hc2)
    have e2 : E * (ρ1 + ρ4) - (ρ4 * (c1 + L) + c2 * (L * ρ1)) = (c1 + L) * ρ1 + c2 * L * ρ4 := by
      rw [hE]; ring
    have e3 : 0 ≤ (c1 + L) * ρ1 + c2 * L * ρ4 := by positivity
    linarith only [t1, t2, e2, e3]
  have hvv : l1Norm (gHat ᵥ* OmHat - gStar ᵥ* OmStar) ≤ F * (ρ1 + ρ4) := by
    have e : gHat ᵥ* OmHat - gStar ᵥ* OmStar =
        (gHat - gStar) ᵥ* OmHat + gStar ᵥ* (OmHat - OmStar) := by
      rw [sub_vecMul, vecMul_sub]; abel
    rw [e]
    refine (l1Norm_add_le _ _).trans ?_
    have t1 : l1Norm ((gHat - gStar) ᵥ* OmHat) ≤ L * ρ1 * (c2 + 1) :=
      (l1Norm_vecMul_le _ _).trans (mul_le_mul h.gd hO (rowSumNorm_nonneg _)
        (mul_nonneg hL hr1))
    have t2 : l1Norm (gStar ᵥ* (OmHat - OmStar)) ≤ c1 * ρ4 :=
      (l1Norm_vecMul_le _ _).trans (mul_le_mul h.g1 h.Od (rowSumNorm_nonneg _) hc1)
    have e2 : F * (ρ1 + ρ4) - (L * ρ1 * (c2 + 1) + c1 * ρ4) = L * (c2 + 1) * ρ4 + c1 * ρ1 := by
      rw [hF]; ring
    have e3 : 0 ≤ L * (c2 + 1) * ρ4 + c1 * ρ1 := by positivity
    linarith only [t1, t2, e2, e3]
  have hC1 : 1 ≤ 1 + Kt + C12 + C11 := by linarith [hKt0]
  have hCa : ∀ x, 0 ≤ x → x ≤ 1 + Kt + C12 + C11 → x * (ρ1 + ρ4) ≤
      (1 + Kt + C12 + C11) * (ρ1 + ρ4) := fun x _ hx => mul_le_mul_of_nonneg_right hx ha0
  refine ⟨?_, ?_, ?_⟩
  · rw [toBlocks₂₂_sub, thetaBlock_22, thetaBlock_22]
    have : -sh⁻¹ - -ss⁻¹ = -(sh⁻¹ - ss⁻¹) := by ring
    rw [this, abs_neg]
    exact ht.trans (hCa Kt hKt0 (by linarith [hC12', hC11']))
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs, toBlocks₁₂_sub, thetaBlock_12, thetaBlock_12]
    have e : sh⁻¹ * (OmHat *ᵥ gHat) k - ss⁻¹ * (OmStar *ᵥ gStar) k =
        (sh⁻¹ - ss⁻¹) * (OmHat *ᵥ gHat) k +
          ss⁻¹ * ((OmHat *ᵥ gHat) k - (OmStar *ᵥ gStar) k) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have a1 : |(sh⁻¹ - ss⁻¹) * (OmHat *ᵥ gHat) k| ≤ Kt * (ρ1 + ρ4) * Mu := by
      rw [abs_mul]
      exact mul_le_mul ht ((abs_le_norm _ k).trans hu) (abs_nonneg _) (by positivity)
    have a2 : |ss⁻¹ * ((OmHat *ᵥ gHat) k - (OmStar *ᵥ gStar) k)| ≤
        1 / c3 * (E * (ρ1 + ρ4)) := by
      rw [abs_mul, abs_of_nonneg hts0]
      refine mul_le_mul hts ?_ (abs_nonneg _) (by positivity)
      exact (abs_le_norm (OmHat *ᵥ gHat - OmStar *ᵥ gStar) k).trans huu
    have : Kt * (ρ1 + ρ4) * Mu + 1 / c3 * (E * (ρ1 + ρ4)) = C12 * (ρ1 + ρ4) := by
      rw [hC12]; field_simp
    have hCaa := hCa C12 hC12' (by linarith only [hKt0, hC12', hC11'])
    linarith only [a1, a2, this, hCaa]
  · have e : (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₁ =
        (OmHat - OmStar) - ((sh⁻¹ - ss⁻¹) • vecMulVec (OmHat *ᵥ gHat) (gHat ᵥ* OmHat)
          + ss⁻¹ • vecMulVec (OmHat *ᵥ gHat - OmStar *ᵥ gStar) (gHat ᵥ* OmHat)
          + ss⁻¹ • vecMulVec (OmStar *ᵥ gStar) (gHat ᵥ* OmHat - gStar ᵥ* OmStar)) := by
      rw [toBlocks₁₁_sub, thetaBlock_11, thetaBlock_11]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.sub_apply, smul_eq_mul]
      ring
    rw [e]
    refine (rowSumNorm_sub_le _ _).trans ?_
    have r1 : rowSumNorm ((sh⁻¹ - ss⁻¹) • vecMulVec (OmHat *ᵥ gHat) (gHat ᵥ* OmHat))
        ≤ Kt * (ρ1 + ρ4) * (Mu * Mu) := by
      refine (rowSumNorm_smul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_left (rowSumNorm_vecMulVec_le _ _) (abs_nonneg _)).trans ?_
      exact mul_le_mul ht (mul_le_mul hu hv (l1Norm_nonneg _) hMu0)
        (mul_nonneg (norm_nonneg _) (l1Norm_nonneg _)) (mul_nonneg hKt0 ha0)
    have r2 : rowSumNorm (ss⁻¹ • vecMulVec (OmHat *ᵥ gHat - OmStar *ᵥ gStar) (gHat ᵥ* OmHat))
        ≤ 1 / c3 * (E * (ρ1 + ρ4) * Mu) := by
      refine (rowSumNorm_smul_le _ _).trans ?_
      rw [abs_of_nonneg hts0]
      refine (mul_le_mul_of_nonneg_left (rowSumNorm_vecMulVec_le _ _) hts0).trans ?_
      exact mul_le_mul hts (mul_le_mul huu hv (l1Norm_nonneg _) (mul_nonneg hE0 ha0))
        (mul_nonneg (norm_nonneg _) (l1Norm_nonneg _)) (by positivity)
    have r3 : rowSumNorm (ss⁻¹ • vecMulVec (OmStar *ᵥ gStar) (gHat ᵥ* OmHat - gStar ᵥ* OmStar))
        ≤ 1 / c3 * (c2 * c1 * (F * (ρ1 + ρ4))) := by
      refine (rowSumNorm_smul_le _ _).trans ?_
      rw [abs_of_nonneg hts0]
      refine (mul_le_mul_of_nonneg_left (rowSumNorm_vecMulVec_le _ _) hts0).trans ?_
      exact mul_le_mul hts (mul_le_mul hus hvv (l1Norm_nonneg _) (mul_nonneg hc2 hc1))
        (mul_nonneg (norm_nonneg _) (l1Norm_nonneg _)) (by positivity)
    have hOd := h.Od
    have key : Kt * (ρ1 + ρ4) * (Mu * Mu) + 1 / c3 * (E * (ρ1 + ρ4) * Mu)
        + 1 / c3 * (c2 * c1 * (F * (ρ1 + ρ4))) + (ρ4) ≤ C11 * (ρ1 + ρ4) := by
      have : Kt * (ρ1 + ρ4) * (Mu * Mu) + 1 / c3 * (E * (ρ1 + ρ4) * Mu)
        + 1 / c3 * (c2 * c1 * (F * (ρ1 + ρ4))) = (C11 - 1) * (ρ1 + ρ4) := by
        rw [hC11]; field_simp; ring
      have e : C11 * (ρ1 + ρ4) = (C11 - 1) * (ρ1 + ρ4) + (ρ1 + ρ4) := by ring
      have e' : ρ4 ≤ ρ1 + ρ4 := by linarith only [hr1]
      linarith only [this, e, e']
    have hCaa := hCa C11 hC11' (by linarith only [hKt0, hC12', hC11'])
    have hr := rowSumNorm_add_le (((sh⁻¹ - ss⁻¹) • vecMulVec (OmHat *ᵥ gHat) (gHat ᵥ* OmHat)
          + ss⁻¹ • vecMulVec (OmHat *ᵥ gHat - OmStar *ᵥ gStar) (gHat ᵥ* OmHat)))
          (ss⁻¹ • vecMulVec (OmStar *ᵥ gStar) (gHat ᵥ* OmHat - gStar ᵥ* OmStar))
    have hr' := rowSumNorm_add_le ((sh⁻¹ - ss⁻¹) • vecMulVec (OmHat *ᵥ gHat) (gHat ᵥ* OmHat))
          (ss⁻¹ • vecMulVec (OmHat *ᵥ gHat - OmStar *ᵥ gStar) (gHat ᵥ* OmHat))
    linarith only [hOd, hr, hr', r1, r2, r3, key, hCaa]

end cor

section calculus

variable {d : ℕ}

lemma contDiff_grad {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (grad F) := by
  rw [contDiff_pi]; intro i
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

lemma clm_apply_eq_sum (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ) :
    ℓ v = ∑ k, v k * ℓ (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : (Pi.single k (v k) : Fin d → ℝ) = v k • Pi.single k (1 : ℝ) := by
    ext j; by_cases h : j = k <;> simp [Pi.single_apply, h]
  rw [this, map_smul, smul_eq_mul]

lemma fderiv_grad_apply {F : (Fin d → ℝ) → ℝ} (θ v : Fin d → ℝ) :
    fderiv ℝ (grad F) θ v = fun i => ∑ k, v k * hess F θ i k := by
  ext i
  have := clm_apply_eq_sum ((ContinuousLinearMap.proj i).comp (fderiv ℝ (grad F) θ)) v
  simpa [hess] using this

lemma fderiv_grad_mulVec {F : (Fin d → ℝ) → ℝ} (θ v : Fin d → ℝ) :
    fderiv ℝ (grad F) θ v = hess F θ *ᵥ v := by
  rw [fderiv_grad_apply]; ext i
  simp [mulVec, dotProduct, mul_comm]

lemma fderiv_apply_grad {f : (Fin d → ℝ) → ℝ} (θ v : Fin d → ℝ) :
    fderiv ℝ f θ v = grad f θ ⬝ᵥ v := by
  rw [clm_apply_eq_sum]
  simp [dotProduct, grad, mul_comm]

lemma grad_taylor {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (th ts : Fin d → ℝ)
    (ρ1 L1 : ℝ) (hρ : ‖th - ts‖ ≤ ρ1) (hL1 : 0 ≤ L1)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      rowSumNorm (hess F (ts + t • (th - ts)) - hess F ts) ≤ L1 * ‖(ts + t • (th - ts)) - ts‖) :
    ‖grad F ts - grad F th + hess F th *ᵥ (th - ts)‖ ≤ 2 * L1 * ρ1 * ρ1 := by
  have hρ0 : 0 ≤ ρ1 := (norm_nonneg _).trans hρ
  have hg := contDiff_grad hF
  let Hc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (hess F th))
  have hHc : ∀ x, Hc x = hess F th *ᵥ x := fun x => rfl
  let φ : (Fin d → ℝ) → (Fin d → ℝ) := fun θ => grad F θ - Hc θ
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x =>
    ((hg.differentiable (by norm_num)) x).sub Hc.differentiableAt
  have hφ' : ∀ x, fderiv ℝ φ x = fderiv ℝ (grad F) x - Hc := fun x => by
    have : HasFDerivAt φ (fderiv ℝ (grad F) x - Hc) x :=
      (((hg.differentiable (by norm_num)) x).hasFDerivAt).sub Hc.hasFDerivAt
    exact this.fderiv
  have hbound : ∀ x ∈ segment ℝ ts th, ‖fderiv ℝ φ x‖ ≤ 2 * L1 * ρ1 := by
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h1 := hlip t ht
    have h2 := hlip 1 ⟨zero_le_one, le_rfl⟩
    have hxn : ‖(ts + t • (th - ts)) - ts‖ ≤ ρ1 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖th - ts‖ ≤ 1 * ‖th - ts‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ ρ1 := by rw [one_mul]; exact hρ
    have h2' : rowSumNorm (hess F th - hess F ts) ≤ L1 * ρ1 := by
      have e1 : ts + (1 : ℝ) • (th - ts) = th := by rw [one_smul]; abel
      rw [e1] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hρ hL1)
    have e : hess F (ts + t • (th - ts)) - hess F th =
        (hess F (ts + t • (th - ts)) - hess F ts) - (hess F th - hess F ts) := by abel
    have h3 : rowSumNorm (hess F (ts + t • (th - ts)) - hess F th) ≤ 2 * L1 * ρ1 := by
      rw [e]
      refine (rowSumNorm_sub_le _ _).trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hxn hL1]
    rw [hφ']
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    have : (fderiv ℝ (grad F) (ts + t • (th - ts)) - Hc) v =
        (hess F (ts + t • (th - ts)) - hess F th) *ᵥ v := by
      rw [ContinuousLinearMap.sub_apply, fderiv_grad_mulVec, hHc, sub_mulVec]
    rw [this]
    exact (mulVec_norm_le _ _).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hφd x) hbound
    (convex_segment ts th) (left_mem_segment ℝ ts th) (right_mem_segment ℝ ts th)
  have e : grad F ts - grad F th + hess F th *ᵥ (th - ts) = -(φ th - φ ts) := by
    simp only [φ, hHc, mulVec_sub]; abel
  rw [e, norm_neg]
  refine hmvt.trans ?_
  calc 2 * L1 * ρ1 * ‖th - ts‖ ≤ 2 * L1 * ρ1 * ρ1 :=
        mul_le_mul_of_nonneg_left hρ (by positivity)

end calculus

section calculus2

variable {d : ℕ}

lemma f_taylor {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (th ts : Fin d → ℝ)
    (ρ1 L2 : ℝ) (hρ : ‖th - ts‖ ≤ ρ1) (hL2 : 0 ≤ L2)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      l1Norm (grad f (ts + t • (th - ts)) - grad f ts) ≤ L2 * ‖(ts + t • (th - ts)) - ts‖) :
    |f ts - f th + grad f th ⬝ᵥ (th - ts)| ≤ 2 * L2 * ρ1 * ρ1 := by
  have hρ0 : 0 ≤ ρ1 := (norm_nonneg _).trans hρ
  let dotL : (Fin d → ℝ) →L[ℝ] ℝ := ∑ k, (grad f th k) • ContinuousLinearMap.proj k
  have hdot : ∀ x, dotL x = grad f th ⬝ᵥ x := by
    intro x; simp [dotL, dotProduct]
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  let ψ : (Fin d → ℝ) → ℝ := fun θ => f θ - dotL θ
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x => (hfd x).sub dotL.differentiableAt
  have hψ' : ∀ x, fderiv ℝ ψ x = fderiv ℝ f x - dotL := fun x => by
    have : HasFDerivAt ψ (fderiv ℝ f x - dotL) x :=
      ((hfd x).hasFDerivAt).sub dotL.hasFDerivAt
    exact this.fderiv
  have hbound : ∀ x ∈ segment ℝ ts th, ‖fderiv ℝ ψ x‖ ≤ 2 * L2 * ρ1 := by
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h1 := hlip t ht
    have h2 := hlip 1 ⟨zero_le_one, le_rfl⟩
    have hxn : ‖(ts + t • (th - ts)) - ts‖ ≤ ρ1 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖th - ts‖ ≤ 1 * ‖th - ts‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ ρ1 := by rw [one_mul]; exact hρ
    have h2' : l1Norm (grad f th - grad f ts) ≤ L2 * ρ1 := by
      have e1 : ts + (1 : ℝ) • (th - ts) = th := by rw [one_smul]; abel
      rw [e1] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hρ hL2)
    have e : grad f (ts + t • (th - ts)) - grad f th =
        (grad f (ts + t • (th - ts)) - grad f ts) - (grad f th - grad f ts) := by abel
    have h3 : l1Norm (grad f (ts + t • (th - ts)) - grad f th) ≤ 2 * L2 * ρ1 := by
      rw [e]
      refine (l1Norm_sub_le _ _).trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hxn hL2]
    rw [hψ']
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    have : (fderiv ℝ f (ts + t • (th - ts)) - dotL) v =
        (grad f (ts + t • (th - ts)) - grad f th) ⬝ᵥ v := by
      rw [ContinuousLinearMap.sub_apply, fderiv_apply_grad, hdot, sub_dotProduct]
    rw [this, Real.norm_eq_abs]
    exact (abs_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψd x) hbound
    (convex_segment ts th) (left_mem_segment ℝ ts th) (right_mem_segment ℝ ts th)
  have e : f ts - f th + grad f th ⬝ᵥ (th - ts) = -(ψ th - ψ ts) := by
    simp only [ψ, hdot, dotProduct_sub]; ring
  rw [e, abs_neg, ← Real.norm_eq_abs]
  refine hmvt.trans ?_
  calc 2 * L2 * ρ1 * ‖th - ts‖ ≤ 2 * L2 * ρ1 * ρ1 :=
        mul_le_mul_of_nonneg_left hρ (by positivity)

end calculus2

section assembly

variable {d : ℕ}

lemma mulVec_inl_apply (M : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (x1 : Fin d → ℝ) (x2 : ℝ)
    (k : Fin d) :
    (M *ᵥ Sum.elim x1 (fun _ => x2)) (Sum.inl k) =
      (M.toBlocks₁₁ *ᵥ x1) k + M.toBlocks₁₂ k () * x2 := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

lemma J1_bound (T : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (x1 : Fin d → ℝ) (x2 B1 B2 R : ℝ)
    (hT11 : rowSumNorm T.toBlocks₁₁ ≤ R) (hT12 : ‖fun k => T.toBlocks₁₂ k ()‖ ≤ R)
    (hx1 : ‖x1‖ ≤ B1) (hx2 : |x2| ≤ B2) :
    ‖fun k => (T *ᵥ Sum.elim x1 (fun _ => x2)) (Sum.inl k)‖ ≤ R * (B1 + B2) := by
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans hx1
  have hB2 : 0 ≤ B2 := (abs_nonneg _).trans hx2
  have hR : 0 ≤ R := (rowSumNorm_nonneg _).trans hT11
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [Real.norm_eq_abs, mulVec_inl_apply]
  refine (abs_add_le _ _).trans ?_
  have a1 : |(T.toBlocks₁₁ *ᵥ x1) k| ≤ R * B1 :=
    (abs_le_norm _ k).trans ((mulVec_norm_le _ _).trans
      (mul_le_mul hT11 hx1 (norm_nonneg _) hR))
  have a2 : |T.toBlocks₁₂ k () * x2| ≤ R * B2 := by
    rw [abs_mul]
    exact mul_le_mul ((abs_le_norm (fun k => T.toBlocks₁₂ k ()) k).trans hT12) hx2
      (abs_nonneg _) hR
  linarith

lemma J2_bound (T : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (x1 : Fin d → ℝ) (x2 B R : ℝ)
    (hT : rowSumNorm T ≤ R) (hx1 : ‖x1‖ ≤ B) (hx2 : |x2| ≤ B) :
    ‖T *ᵥ Sum.elim x1 (fun _ => x2)‖ ≤ R * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hx1
  have hn : ‖(Sum.elim x1 (fun _ => x2) : Fin d ⊕ Unit → ℝ)‖ ≤ B := by
    rw [pi_norm_le_iff_of_nonneg hB]
    rintro (k | u)
    · simpa using (norm_le_pi_norm x1 k).trans hx1
    · simpa using hx2
  calc ‖T *ᵥ Sum.elim x1 (fun _ => x2)‖
      ≤ rowSumNorm T * ‖(Sum.elim x1 (fun _ => x2) : Fin d ⊕ Unit → ℝ)‖ := mulVec_norm_le _ _
    _ ≤ rowSumNorm T * B := mul_le_mul_of_nonneg_left hn (rowSumNorm_nonneg _)
    _ ≤ R * B := mul_le_mul_of_nonneg_right hT hB

lemma J3_block11 (Om H : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (1 - thetaBlock Om g * borderedHessian H g).toBlocks₁₁ =
      (1 - Om * H) - (g ⬝ᵥ (Om *ᵥ g))⁻¹ • vecMulVec (Om *ᵥ g) (g ᵥ* (1 - Om * H)) := by
  have h1 : (1 : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ).toBlocks₁₁ = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  rw [toBlocks₁₁_sub, h1, thetaBlock_eq]
  unfold borderedHessian
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  have e1 : replicateCol Unit ((g ⬝ᵥ (Om *ᵥ g))⁻¹ • (Om *ᵥ g)) * replicateRow Unit g =
      (g ⬝ᵥ (Om *ᵥ g))⁻¹ • vecMulVec (Om *ᵥ g) g := by
    rw [← vecMulVec_eq Unit, smul_vecMulVec]
  have e2 : (Om - (g ⬝ᵥ (Om *ᵥ g))⁻¹ • vecMulVec (Om *ᵥ g) (g ᵥ* Om)) * H =
      Om * H - (g ⬝ᵥ (Om *ᵥ g))⁻¹ • vecMulVec (Om *ᵥ g) ((g ᵥ* Om) ᵥ* H) := by
    rw [sub_mul, smul_mul, vecMulVec_mul]
  have e3 : g ᵥ* (1 - Om * H) = g - (g ᵥ* Om) ᵥ* H := by
    rw [vecMul_sub, vecMul_one, vecMul_vecMul]
  rw [e1, e2, e3]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.sub_apply, smul_eq_mul]
  ring

end assembly

theorem corollary_3_1 (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
        (ρ1 ρ4 : ℝ),
        0 ≤ ρ1 → 0 ≤ ρ4 → ρ1 + ρ4 ≤ δ →
        l1Norm gStar ≤ c1 → l1Norm (gHat - gStar) ≤ L2 * ρ1 →
        rowSumNorm OmStar ≤ c2 → c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        |(thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₂₂ () ()|
            ≤ C * (ρ1 + ρ4) ∧
        ‖fun k => (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₂ k ()‖
            ≤ C * (ρ1 + ρ4) ∧
        rowSumNorm (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₁
            ≤ C * (ρ1 + ρ4) := by
  obtain ⟨C, δ, hC, hδ, hδ1, H⟩ := cor_aux (max c1 0) (max c2 0) c3 (max L2 0)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hc3
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro d OmHat OmStar gHat gStar ρ1 ρ4 h1 h4 hs hg1 hgd hO2 hc3s hOd
  exact H d OmHat OmStar gHat gStar ρ1 ρ4
    ⟨h1, h4, hg1.trans (le_max_left _ _),
      hgd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h1),
      hO2.trans (le_max_left _ _), hOd⟩ hs hc3s


set_option maxHeartbeats 1000000 in
theorem lemma_A_1 (c1 c2 c3 L1 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (F f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
        (thetaHat thetaStar : Fin d → ℝ) (ρ1 ρ2 ρ3 ρ4 ρ5 : ℝ),
        ContDiff ℝ 2 F → ContDiff ℝ 1 f → f thetaStar = 0 →
        0 ≤ ρ1 → 0 ≤ ρ2 → 0 ≤ ρ3 → 0 ≤ ρ4 → 0 ≤ ρ5 → ρ1 + ρ4 ≤ δ →
        ‖thetaHat - thetaStar‖ ≤ ρ1 →
        ‖grad F thetaStar‖ ≤ ρ2 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          rowSumNorm (hess F (thetaStar + t • (thetaHat - thetaStar)) - hess F thetaStar)
            ≤ L1 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        l1Norm (grad f thetaStar) ≤ c1 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          l1Norm (grad f (thetaStar + t • (thetaHat - thetaStar)) - grad f thetaStar)
            ≤ L2 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        rowSumNorm (1 - OmHat * hess F thetaHat) ≤ ρ3 →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm OmStar ≤ c2 →
        c3 ≤ grad f thetaStar ⬝ᵥ (OmStar *ᵥ grad f thetaStar) →
        rowSumNorm (thetaBlock OmStar (grad f thetaStar)) ≤ ρ5 →
        ‖fun k => remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) ∧
        ‖remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar‖
            ≤ C * (ρ1 ^ 2 * ρ5) ∧
        ‖fun k => remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * (ρ1 * ρ3) ∧
        ‖fun k => (remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ2 (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ3 (thetaBlock OmHat (grad f thetaHat))
              (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar) (Sum.inl k)‖
            ≤ C * (ρ1 ^ 2 * ρ5 + (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) + ρ1 * ρ3) := by
  set c1' := max c1 0 with hc1'
  set c2' := max c2 0 with hc2'
  set L1' := max L1 0 with hL1'
  set L2' := max L2 0 with hL2'
  have hc1'0 : 0 ≤ c1' := le_max_right _ _
  have hc2'0 : 0 ≤ c2' := le_max_right _ _
  have hL1'0 : 0 ≤ L1' := le_max_right _ _
  have hL2'0 : 0 ≤ L2' := le_max_right _ _
  obtain ⟨Cc, δc, hCc, hδc, hδc1, Hc⟩ := cor_aux c1' c2' c3 L2' hc1'0 hc2'0 hL2'0 hc3
  obtain ⟨δs, hδs, hδs1, Hs⟩ := s_lower c1' c2' c3 L2' hc1'0 hc2'0 hL2'0 hc3
  set Mg := c1' + L2' with hMg
  set Mu := (c2' + 1) * Mg with hMu
  have hMg0 : 0 ≤ Mg := by positivity
  have hMu0 : 0 ≤ Mu := by positivity
  set K3 := 1 + 2 / c3 * Mu * Mg with hK3
  set C1 := Cc * (1 + 2 * L1' + 2 * L2') with hC1
  set C2 := 2 * (L1' + L2') with hC2
  have hK30 : 0 ≤ K3 := by positivity
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨1 + C1 + C2 + K3, min δc δs, by positivity, lt_min hδc hδs, ?_⟩
  intro d F f OmHat OmStar thetaHat thetaStar ρ1 ρ2 ρ3 ρ4 ρ5 hF hf hfs h1 h2 h3 h4 h5 hsum hθ
    hgF hlipH hgf hlipg hOm3 hOm4 hOm2 hc3s h5'
  have hCle1 : C1 ≤ 1 + C1 + C2 + K3 := by linarith
  have hCle2 : C2 ≤ 1 + C1 + C2 + K3 := by linarith
  have hCle3 : K3 ≤ 1 + C1 + C2 + K3 := by linarith
  have ha_c : ρ1 + ρ4 ≤ δc := hsum.trans (min_le_left _ _)
  have ha_s : ρ1 + ρ4 ≤ δs := hsum.trans (min_le_right _ _)
  have ha1 : ρ1 + ρ4 ≤ 1 := ha_c.trans hδc1
  have ha0 : 0 ≤ ρ1 + ρ4 := add_nonneg h1 h4
  have hdiff : l1Norm (grad f thetaHat - grad f thetaStar) ≤ L2' * ρ1 := by
    have := hlipg 1 ⟨zero_le_one, le_rfl⟩
    have e1 : thetaStar + (1 : ℝ) • (thetaHat - thetaStar) = thetaHat := by rw [one_smul]; abel
    rw [e1] at this
    exact this.trans ((mul_le_mul_of_nonneg_right (le_max_left L2 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hθ hL2'0))
  have hcond : Cond c1' c2' L2' OmHat OmStar (grad f thetaHat) (grad f thetaStar) ρ1 ρ4 :=
    ⟨h1, h4, hgf.trans (le_max_left _ _), hdiff, hOm2.trans (le_max_left _ _), hOm4⟩
  obtain ⟨c22, c12, c11⟩ := Hc d OmHat OmStar _ _ ρ1 ρ4 hcond ha_c hc3s
  have hs_hat := Hs d OmHat OmStar _ _ ρ1 ρ4 hcond ha_s hc3s
  have hlipH' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      rowSumNorm (hess F (thetaStar + t • (thetaHat - thetaStar)) - hess F thetaStar)
        ≤ L1' * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖ :=
    fun t ht => (hlipH t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left L1 0) (norm_nonneg _))
  have hlipg' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      l1Norm (grad f (thetaStar + t • (thetaHat - thetaStar)) - grad f thetaStar)
        ≤ L2' * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖ :=
    fun t ht => (hlipg t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left L2 0) (norm_nonneg _))
  have tF := grad_taylor hF thetaHat thetaStar ρ1 L1' hθ hL1'0 hlipH'
  have tf0 := f_taylor hf thetaHat thetaStar ρ1 L2' hθ hL2'0 hlipg'
  have hx1 : ‖-grad F thetaHat + hess F thetaHat *ᵥ (thetaHat - thetaStar)‖
      ≤ ρ2 + 2 * L1' * ρ1 * ρ1 := by
    have e : -grad F thetaHat + hess F thetaHat *ᵥ (thetaHat - thetaStar) =
        -(grad F thetaStar) +
          (grad F thetaStar - grad F thetaHat + hess F thetaHat *ᵥ (thetaHat - thetaStar)) := by
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  have hx2 : |-f thetaHat + grad f thetaHat ⬝ᵥ (thetaHat - thetaStar)| ≤ 2 * L2' * ρ1 * ρ1 := by
    have e : f thetaStar - f thetaHat + grad f thetaHat ⬝ᵥ (thetaHat - thetaStar) =
        -f thetaHat + grad f thetaHat ⬝ᵥ (thetaHat - thetaStar) := by rw [hfs]; ring
    have tf1 := tf0
    rw [e] at tf1; exact tf1
  have X0 : 0 ≤ (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) := by positivity
  have Y0 : 0 ≤ ρ1 ^ 2 * ρ5 := by positivity
  have Z0 : 0 ≤ ρ1 * ρ3 := by positivity
  -- J1
  have b1 : ‖fun k => remJ1 (thetaBlock OmHat (grad f thetaHat))
            (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C1 * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) := by
    unfold remJ1
    refine (J1_bound _ _ _ (ρ2 + 2 * L1' * ρ1 * ρ1) (2 * L2' * ρ1 * ρ1) (Cc * (ρ1 + ρ4))
      c11 c12 hx1 hx2).trans ?_
    have h : (ρ2 + 2 * L1' * ρ1 * ρ1) + 2 * L2' * ρ1 * ρ1 ≤
        (1 + 2 * L1' + 2 * L2') * (ρ1 ^ 2 + ρ2) := by
      have e : (1 + 2 * L1' + 2 * L2') * (ρ1 ^ 2 + ρ2) -
          ((ρ2 + 2 * L1' * ρ1 * ρ1) + 2 * L2' * ρ1 * ρ1) = 2 * L1' * ρ2 + 2 * L2' * ρ2 + ρ1 ^ 2 := by
        ring
      have e0 : 0 ≤ 2 * L1' * ρ2 + 2 * L2' * ρ2 + ρ1 ^ 2 := by positivity
      linarith only [e, e0]
    calc Cc * (ρ1 + ρ4) * ((ρ2 + 2 * L1' * ρ1 * ρ1) + 2 * L2' * ρ1 * ρ1)
        ≤ Cc * (ρ1 + ρ4) * ((1 + 2 * L1' + 2 * L2') * (ρ1 ^ 2 + ρ2)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C1 * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) := by rw [hC1]; ring
  -- J2
  have b2 : ‖remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar‖
            ≤ C2 * (ρ1 ^ 2 * ρ5) := by
    unfold remJ2
    have hB1 : 0 ≤ 2 * L2' * ρ1 * ρ1 := by positivity
    have hB2 : 0 ≤ 2 * L1' * ρ1 * ρ1 := by positivity
    refine (J2_bound _ _ _ (2 * L1' * ρ1 * ρ1 + 2 * L2' * ρ1 * ρ1) ρ5 h5' ?_ ?_).trans ?_
    · linarith
    · exact tf0.trans (by linarith)
    · exact le_of_eq (by rw [hC2]; ring)
  -- J3
  have hsh : 0 < grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat) := by linarith
  have ht : (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹ ≤ 2 / c3 := by
    have := inv_anti₀ (by positivity : 0 < c3 / 2) hs_hat
    calc _ ≤ (c3 / 2)⁻¹ := this
      _ = 2 / c3 := by rw [inv_div]
  have ht0 : 0 ≤ (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹ := inv_nonneg.2 hsh.le
  have hgl1 := hcond.l1_hat hL2'0 ha1
  have hgn : ‖grad f thetaHat‖ ≤ Mg := (norm_le_l1Norm _).trans hgl1
  have hu : ‖OmHat *ᵥ grad f thetaHat‖ ≤ Mu :=
    (mulVec_norm_le _ _).trans (mul_le_mul (hcond.rs_hat ha1) hgn (norm_nonneg _) (by positivity))
  have hw : l1Norm (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat)) ≤ Mg * ρ3 :=
    (l1Norm_vecMul_le _ _).trans (mul_le_mul hgl1 hOm3 (rowSumNorm_nonneg _) hMg0)
  have hM : rowSumNorm ((1 - OmHat * hess F thetaHat) -
      (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹ •
        vecMulVec (OmHat *ᵥ grad f thetaHat) (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat)))
      ≤ K3 * ρ3 := by
    refine (rowSumNorm_sub_le _ _).trans ?_
    have h1' := rowSumNorm_smul_le (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹
      (vecMulVec (OmHat *ᵥ grad f thetaHat) (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat)))
    rw [abs_of_nonneg ht0] at h1'
    have h2' := rowSumNorm_vecMulVec_le (OmHat *ᵥ grad f thetaHat)
      (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat))
    have h3' : (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹ *
        rowSumNorm (vecMulVec (OmHat *ᵥ grad f thetaHat)
          (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat))) ≤ 2 / c3 * (Mu * (Mg * ρ3)) :=
      mul_le_mul ht (h2'.trans (mul_le_mul hu hw (l1Norm_nonneg _) hMu0)) (rowSumNorm_nonneg _)
        (by positivity)
    have : K3 * ρ3 = ρ3 + 2 / c3 * (Mu * (Mg * ρ3)) := by rw [hK3]; ring
    linarith
  have b3 : ‖fun k => remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar (Sum.inl k)‖
            ≤ K3 * (ρ1 * ρ3) := by
    unfold remJ3
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs, mulVec_inl_apply, mul_zero, add_zero, J3_block11]
    calc _ ≤ ‖(((1 - OmHat * hess F thetaHat) -
      (grad f thetaHat ⬝ᵥ (OmHat *ᵥ grad f thetaHat))⁻¹ •
        vecMulVec (OmHat *ᵥ grad f thetaHat) (grad f thetaHat ᵥ* (1 - OmHat * hess F thetaHat)))
          *ᵥ (thetaHat - thetaStar))‖ := abs_le_norm _ k
      _ ≤ _ := mulVec_norm_le _ _
      _ ≤ K3 * ρ3 * ρ1 := mul_le_mul hM hθ (norm_nonneg _) (by positivity)
      _ = K3 * (ρ1 * ρ3) := by ring
  have b2' : ‖fun k => remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C2 * (ρ1 ^ 2 * ρ5) := by
    refine le_trans ?_ b2
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    exact norm_le_pi_norm (remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar) (Sum.inl k)
  refine ⟨b1.trans (mul_le_mul_of_nonneg_right hCle1 X0), b2.trans
    (mul_le_mul_of_nonneg_right hCle2 Y0), b3.trans (mul_le_mul_of_nonneg_right hCle3 Z0), ?_⟩
  refine (norm_add_le_of_le (norm_add_le_of_le b1 b2') b3).trans ?_
  have q1 := mul_nonneg (sub_nonneg.2 hCle1) X0
  have q2 := mul_nonneg (sub_nonneg.2 hCle2) Y0
  have q3 := mul_nonneg (sub_nonneg.2 hCle3) Z0
  have eq : (1 + C1 + C2 + K3) * (ρ1 ^ 2 * ρ5 + (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) + ρ1 * ρ3) -
      (C1 * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) + C2 * (ρ1 ^ 2 * ρ5) + K3 * (ρ1 * ρ3)) =
      ((1 + C1 + C2 + K3) - C1) * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) +
      ((1 + C1 + C2 + K3) - C2) * (ρ1 ^ 2 * ρ5) + ((1 + C1 + C2 + K3) - K3) * (ρ1 * ρ3) := by
    ring
  linarith only [q1, q2, q3, eq]


end LagrangeRank.Debias

open LagrangeRank.Debias
open Matrix

theorem solution (c1 c2 c3 L1 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (F f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
        (thetaHat thetaStar : Fin d → ℝ) (ρ1 ρ2 ρ3 ρ4 ρ5 : ℝ),
        ContDiff ℝ 2 F → ContDiff ℝ 1 f → f thetaStar = 0 →
        0 ≤ ρ1 → 0 ≤ ρ2 → 0 ≤ ρ3 → 0 ≤ ρ4 → 0 ≤ ρ5 → ρ1 + ρ4 ≤ δ →
        ‖thetaHat - thetaStar‖ ≤ ρ1 →
        ‖grad F thetaStar‖ ≤ ρ2 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          rowSumNorm (hess F (thetaStar + t • (thetaHat - thetaStar)) - hess F thetaStar)
            ≤ L1 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        l1Norm (grad f thetaStar) ≤ c1 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          l1Norm (grad f (thetaStar + t • (thetaHat - thetaStar)) - grad f thetaStar)
            ≤ L2 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        rowSumNorm (1 - OmHat * hess F thetaHat) ≤ ρ3 →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm OmStar ≤ c2 →
        c3 ≤ grad f thetaStar ⬝ᵥ (OmStar *ᵥ grad f thetaStar) →
        rowSumNorm (thetaBlock OmStar (grad f thetaStar)) ≤ ρ5 →
        ‖fun k => remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) ∧
        ‖remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar‖
            ≤ C * (ρ1 ^ 2 * ρ5) ∧
        ‖fun k => remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * (ρ1 * ρ3) ∧
        ‖fun k => (remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ2 (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ3 (thetaBlock OmHat (grad f thetaHat))
              (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar) (Sum.inl k)‖
            ≤ C * (ρ1 ^ 2 * ρ5 + (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) + ρ1 * ρ3) :=
  LagrangeRank.Debias.lemma_A_1 c1 c2 c3 L1 L2 hc3
