-- Prove2me | solution 1 for LagrangeRank.Debias.corollary_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:28:18.481717+00:00
-- url     : https://prove2.me/submissions/a43be752-16ff-4061-93b7-e60e0ecf0c91

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



end LagrangeRank.Debias

open LagrangeRank.Debias
open Matrix

theorem solution (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
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
            ≤ C * (ρ1 + ρ4) :=
  LagrangeRank.Debias.corollary_3_1 c1 c2 c3 L2 hc3
