-- Prove2me | solution 1 for GilmoreGomory61.CuttingStock.step3_slack_test
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:34:22.700139+00:00
-- url     : https://prove2.me/submissions/35738827-ce74-47a1-82ec-720c816cd565

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

open Classical

namespace GilmoreGomory61.CuttingStock

section LA
variable {m k : ℕ} (I : Instance m k) (β : Fin m → Col I)

lemma gg_bordered_inv (hβ : IsUnit (basisMat I β).det) :
    (bordered I β)⁻¹ =
      Matrix.fromBlocks 1
        (Matrix.of fun _ r => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
        0 (basisMat I β)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  unfold bordered
  rw [Matrix.fromBlocks_multiply]
  have hA : basisMat I β * (basisMat I β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hβ
  have h2 : Matrix.of (fun (_ : Unit) (r : Fin m) => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
      + Matrix.of (fun (_ : Unit) (r : Fin m) => -costRow I β r) * (basisMat I β)⁻¹ = 0 := by
    ext u r
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA, h2]
  exact Matrix.fromBlocks_one

lemma gg_mult (hβ : IsUnit (basisMat I β).det) :
    mult I β = Matrix.vecMul (costRow I β) (basisMat I β)⁻¹ := by
  funext i
  unfold mult
  rw [gg_bordered_inv I β hβ]
  simp


def gg_Nvec (I : Instance m k) : Fin m → ℝ := fun i => (I.N i : ℝ)

lemma gg_nbar_inr (hβ : IsUnit (basisMat I β).det) (r : Fin m) :
    Nbar I β (Sum.inr r) = (Matrix.mulVec (basisMat I β)⁻¹ (gg_Nvec I)) r := by
  unfold Nbar
  rw [gg_bordered_inv I β hβ]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Nprime, gg_Nvec]

lemma gg_nbar_inl (hβ : IsUnit (basisMat I β).det) :
    Nbar I β (Sum.inl ()) = ∑ i, mult I β i * (I.N i : ℝ) := by
  unfold Nbar
  rw [gg_bordered_inv I β hβ, gg_mult I β hβ]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Nprime]

lemma gg_priceOut (hβ : IsUnit (basisMat I β).det) (j : Col I) :
    priceOut I β j = (∑ i, mult I β i * colVec I j i) - colCost I j := by
  unfold priceOut
  rw [gg_bordered_inv I β hβ, gg_mult I β hβ]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, extCol]
  ring

/-- general finitely supported solution built from basis coefficients and one extra column -/
noncomputable def zmk (j : Col I) (a : Fin m → ℝ) (t : ℝ) : Col I →₀ ℝ :=
  ∑ r : Fin m, Finsupp.single (β r) (a r) + Finsupp.single j t

lemma sum_zmk (j : Col I) (a : Fin m → ℝ) (t : ℝ) (f : Col I → ℝ) :
    (zmk I β j a t).sum (fun j' v => f j' * v) = ∑ r, f (β r) * a r + f j * t := by
  unfold zmk
  rw [Finsupp.sum_add_index' (by intro _; simp) (by intros; ring)]
  rw [← Finsupp.sum_finsetSum_index (by intro _; simp) (by intros; ring)]
  simp [Finsupp.sum_single_index]

lemma zmk_nonneg (j : Col I) (a : Fin m → ℝ) (t : ℝ) (ha : ∀ r, 0 ≤ a r) (ht : 0 ≤ t) (j' : Col I) :
    0 ≤ zmk I β j a t j' := by
  unfold zmk
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply]
  apply add_nonneg
  · apply Finset.sum_nonneg; intro r _
    rw [Finsupp.single_apply]; split_ifs
    · exact ha r
    · exact le_rfl
  · rw [Finsupp.single_apply]; split_ifs
    · exact ht
    · exact le_rfl

lemma zmk_support (j : Col I) (a : Fin m → ℝ) (t : ℝ) :
    ∀ j' ∈ (zmk I β j a t).support, j' ∈ Set.range β ∨ j' = j := by
  intro j' hj'
  unfold zmk at hj'
  have := Finsupp.support_add hj'
  rcases Finset.mem_union.1 this with h | h
  · have := Finsupp.support_finset_sum h
    obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.1 this
    have := Finsupp.support_single_subset hr
    left; exact ⟨r, (Finset.mem_singleton.1 this).symm⟩
  · have := Finsupp.support_single_subset h
    right; exact Finset.mem_singleton.1 this

lemma gg_mult_dot (hβ : IsUnit (basisMat I β).det) (v : Fin m → ℝ) :
    ∑ i, mult I β i * v i = ∑ r, costRow I β r * (Matrix.mulVec (basisMat I β)⁻¹ v) r := by
  rw [gg_mult I β hβ]
  have := Matrix.dotProduct_mulVec (costRow I β) (basisMat I β)⁻¹ v
  unfold dotProduct at this
  exact this.symm

lemma gg_sum_basic (a : Fin m → ℝ) (f : Col I → ℝ) :
    (∑ r : Fin m, Finsupp.single (β r) (a r)).sum (fun j' v => f j' * v) =
      ∑ r, f (β r) * a r := by
  rw [← Finsupp.sum_finsetSum_index (by intro _; simp) (by intros; ring)]
  simp [Finsupp.sum_single_index]

lemma gg_cost_basic (hβ : IsUnit (basisMat I β).det) :
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) := by
  unfold cost basicSol
  rw [gg_sum_basic I β _ (colCost I), gg_nbar_inl I β hβ, gg_mult_dot I β hβ]
  simp only [costRow, gg_nbar_inr I β hβ]
  rfl

lemma gg_cons_basic (hβ : IsUnit (basisMat I β).det) (i : Fin m) :
    ((basicSol I β).sum fun j v => colVec I j i * v) = (I.N i : ℝ) := by
  unfold basicSol
  rw [gg_sum_basic I β _ (fun j => colVec I j i)]
  have h1 : ∀ r, Nbar I β (Sum.inr r) = (Matrix.mulVec (basisMat I β)⁻¹ (gg_Nvec I)) r :=
    gg_nbar_inr I β hβ
  simp only [h1]
  have h2 := congrFun (Matrix.mulVec_mulVec (gg_Nvec I) (basisMat I β) (basisMat I β)⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hβ, Matrix.one_mulVec] at h2
  have h3 : (I.N i : ℝ) = gg_Nvec I i := rfl
  rw [h3, ← h2]
  simp [Matrix.mulVec, dotProduct, basisMat, gg_Nvec]

theorem gg_first_row {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsUnit (basisMat I β).det) :
    (bordered I β)⁻¹ =
      Matrix.fromBlocks 1
        (Matrix.of fun _ r => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
        0 (basisMat I β)⁻¹ ∧
    mult I β = Matrix.vecMul (costRow I β) (basisMat I β)⁻¹ ∧
    (∀ j : Col I, priceOut I β j =
      (∑ i, mult I β i * colVec I j i) - colCost I j) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    (∀ i, ((basicSol I β).sum fun j v => colVec I j i * v) = (I.N i : ℝ)) :=
  ⟨gg_bordered_inv I β hβ, gg_mult I β hβ, gg_priceOut I β hβ, gg_cost_basic I β hβ,
    gg_cons_basic I β hβ⟩


lemma gg_inj (hβ : IsUnit (basisMat I β).det) : Function.Injective β := by
  intro r s hrs
  by_contra hne
  have := Matrix.det_zero_of_column_eq hne (M := basisMat I β) (by
    intro k; simp [basisMat, hrs])
  rw [this] at hβ
  exact not_isUnit_zero hβ

lemma gg_sum_supp1 (hβ : IsUnit (basisMat I β).det) (z : Col I →₀ ℝ) (j : Col I)
    (hs : ∀ j' ∈ z.support, j' ∈ Set.range β ∨ j' = j) (hj : j ∉ Set.range β) (f : Col I → ℝ) :
    z.sum (fun j' v => f j' * v) = ∑ r, f (β r) * z (β r) + f j * z j := by
  have hsub : z.support ⊆ insert j (Finset.univ.image β) := by
    intro j' hj'
    rcases hs j' hj' with ⟨r, rfl⟩ | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ r))
    · exact Finset.mem_insert_self _ _
  rw [Finsupp.sum_of_support_subset z hsub _ (by intros; simp)]
  have hn : j ∉ Finset.univ.image β := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro r hr; exact hj ⟨r, hr⟩
  rw [Finset.sum_insert hn, Finset.sum_image (fun a _ b _ h => gg_inj I β hβ h), add_comm]

lemma gg_sum_supp2 (hβ : IsUnit (basisMat I β).det) (z : Col I →₀ ℝ)
    (hs : ∀ j' ∈ z.support, j' ∈ Set.range β) (f : Col I → ℝ) :
    z.sum (fun j' v => f j' * v) = ∑ r, f (β r) * z (β r) := by
  have hsub : z.support ⊆ Finset.univ.image β := by
    intro j' hj'
    obtain ⟨r, rfl⟩ := hs j' hj'
    exact Finset.mem_image_of_mem _ (Finset.mem_univ r)
  rw [Finsupp.sum_of_support_subset z hsub _ (by intros; simp)]
  rw [Finset.sum_image (fun a _ b _ h => gg_inj I β hβ h)]

lemma gg_Ainv_A (hβ : IsUnit (basisMat I β).det) (v : Fin m → ℝ) :
    Matrix.mulVec (basisMat I β)⁻¹ (Matrix.mulVec (basisMat I β) v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hβ, Matrix.one_mulVec]

lemma gg_A_Ainv (hβ : IsUnit (basisMat I β).det) (v : Fin m → ℝ) :
    Matrix.mulVec (basisMat I β) (Matrix.mulVec (basisMat I β)⁻¹ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hβ, Matrix.one_mulVec]

lemma gg_basic_price (hβ : IsUnit (basisMat I β).det) (r0 : Fin m) :
    ∑ k, mult I β k * colVec I (β r0) k = colCost I (β r0) := by
  rw [gg_mult_dot I β hβ]
  have hv : colVec I (β r0) = Matrix.mulVec (basisMat I β) (Pi.single r0 1) := by
    funext k; simp [Matrix.mulVec, dotProduct, basisMat, Pi.single_apply]
  rw [hv, gg_Ainv_A I β hβ]
  simp [costRow, Pi.single_apply]

/-- nonbasic column: structure of any feasible competitor using the basis plus column j -/
lemma gg_key (hβ : IsUnit (basisMat I β).det) (j : Col I) (hj : j ∉ Set.range β)
    (z : Col I →₀ ℝ) (hz : Feasible I z)
    (hs : ∀ j' ∈ z.support, j' ∈ Set.range β ∨ j' = j) :
    cost I z = cost I (basicSol I β) +
      z j * (colCost I j - ∑ r, costRow I β r *
        (Matrix.mulVec (basisMat I β)⁻¹ (colVec I j)) r) := by
  set Ai := (basisMat I β)⁻¹ with hAi
  set U := Matrix.mulVec Ai (colVec I j) with hU
  set x : Fin m → ℝ := fun r => Nbar I β (Sum.inr r) with hx
  have hxx : x = Matrix.mulVec Ai (gg_Nvec I) := by
    funext r; exact gg_nbar_inr I β hβ r
  have hy : Matrix.mulVec (basisMat I β) (fun r => z (β r)) =
      gg_Nvec I - z j • colVec I j := by
    funext i
    have h1 := hz.2 i
    rw [gg_sum_supp1 I β hβ z j hs hj (fun j' => colVec I j' i)] at h1
    simp only [Matrix.mulVec, dotProduct, basisMat, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, gg_Nvec]
    linarith
  have hy2 : (fun r => z (β r)) = fun r => x r - z j * U r := by
    have := congrArg (Matrix.mulVec Ai) hy
    rw [gg_Ainv_A I β hβ, Matrix.mulVec_sub, Matrix.mulVec_smul, ← hxx] at this
    funext r
    have := congrFun this r
    simpa [hU] using this
  have hc : cost I z = ∑ r, costRow I β r * z (β r) + colCost I j * z j :=
    gg_sum_supp1 I β hβ z j hs hj (colCost I)
  have hb : cost I (basicSol I β) = ∑ r, costRow I β r * x r := by
    unfold cost basicSol
    rw [gg_sum_basic I β _ (colCost I)]
    rfl
  rw [hc, hb]
  have : ∀ r, z (β r) = x r - z j * U r := fun r => congrFun hy2 r
  simp only [this]
  have : ∑ r, costRow I β r * (x r - z j * U r) =
      ∑ r, costRow I β r * x r - z j * ∑ r, costRow I β r * U r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [this]; ring

lemma gg_key_basic (hβ : IsUnit (basisMat I β).det)
    (z : Col I →₀ ℝ) (hz : Feasible I z)
    (hs : ∀ j' ∈ z.support, j' ∈ Set.range β) :
    cost I z = cost I (basicSol I β) := by
  set Ai := (basisMat I β)⁻¹ with hAi
  have hxx : (fun r => Nbar I β (Sum.inr r)) = Matrix.mulVec Ai (gg_Nvec I) := by
    funext r; exact gg_nbar_inr I β hβ r
  have hy : Matrix.mulVec (basisMat I β) (fun r => z (β r)) = gg_Nvec I := by
    funext i
    have h1 := hz.2 i
    rw [gg_sum_supp2 I β hβ z hs (fun j' => colVec I j' i)] at h1
    simp only [Matrix.mulVec, dotProduct, basisMat, Matrix.of_apply, gg_Nvec]
    linarith
  have hy2 : (fun r => z (β r)) = fun r => Nbar I β (Sum.inr r) := by
    have := congrArg (Matrix.mulVec Ai) hy
    rw [gg_Ainv_A I β hβ, ← hxx] at this
    exact this
  have hc : cost I z = ∑ r, costRow I β r * z (β r) :=
    gg_sum_supp2 I β hβ z hs (colCost I)
  have hb : cost I (basicSol I β) = ∑ r, costRow I β r * Nbar I β (Sum.inr r) := by
    unfold cost basicSol
    rw [gg_sum_basic I β _ (colCost I)]
    rfl
  rw [hc, hb]
  have : ∀ r, z (β r) = Nbar I β (Sum.inr r) := fun r => congrFun hy2 r
  simp only [this]


lemma gg_crit1 (hβ : IsFeasibleBasis I β) (j : Col I) (h : Improves I β j) :
    j ∉ Set.range β ∧ colCost I j < ∑ k, mult I β k * colVec I j k := by
  obtain ⟨z, hz, hs, hlt⟩ := h
  have hd := hβ.1
  have hj : j ∉ Set.range β := by
    intro hj
    have hs' : ∀ j' ∈ z.support, j' ∈ Set.range β := by
      intro j' hj'
      rcases hs j' hj' with h | rfl
      · exact h
      · exact hj
    rw [gg_key_basic I β hd z hz hs'] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hj, ?_⟩
  rw [gg_key I β hd j hj z hz hs, ← gg_mult_dot I β hd] at hlt
  by_contra hc
  push_neg at hc
  have : 0 ≤ z j * (colCost I j - ∑ k, mult I β k * colVec I j k) :=
    mul_nonneg (hz.1 j) (by linarith)
  linarith

lemma gg_crit2 (hβ : IsFeasibleBasis I β) (hnd : IsNondegenerate I β) (j : Col I)
    (hj : j ∉ Set.range β) (hc : colCost I j < ∑ k, mult I β k * colVec I j k) :
    Improves I β j := by
  have hd := hβ.1
  set Ai := (basisMat I β)⁻¹ with hAi
  set U := Matrix.mulVec Ai (colVec I j) with hU
  set x : Fin m → ℝ := fun r => Nbar I β (Sum.inr r) with hx
  have hxx : x = Matrix.mulVec Ai (gg_Nvec I) := by
    funext r; exact gg_nbar_inr I β hd r
  have hxpos : ∀ r, 0 < x r := hnd
  rw [gg_mult_dot I β hd] at hc
  set S : ℝ := ∑ r, |U r| / x r with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun r _ => div_nonneg (abs_nonneg _) (hxpos r).le)
  set t : ℝ := 1 / (1 + S) with ht
  have ht0 : 0 < t := by positivity
  have htS : t * S ≤ 1 := by
    rw [ht, one_div, inv_mul_le_iff₀ (by positivity)]; linarith
  have hle : ∀ r, t * U r ≤ x r := by
    intro r
    have h1 : |U r| / x r ≤ S :=
      Finset.single_le_sum (f := fun r => |U r| / x r) (fun r _ => div_nonneg (abs_nonneg _) (hxpos r).le)
        (Finset.mem_univ r)
    have h2 : |U r| ≤ S * x r := by
      rw [div_le_iff₀ (hxpos r)] at h1; exact h1
    calc t * U r ≤ t * |U r| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
      _ ≤ t * (S * x r) := mul_le_mul_of_nonneg_left h2 ht0.le
      _ = (t * S) * x r := by ring
      _ ≤ 1 * x r := mul_le_mul_of_nonneg_right htS (hxpos r).le
      _ = x r := one_mul _
  refine ⟨zmk I β j (fun r => x r - t * U r) t, ⟨?_, ?_⟩, zmk_support I β j _ _, ?_⟩
  · exact zmk_nonneg I β j _ _ (fun r => by linarith [hle r]) ht0.le
  · intro i
    rw [sum_zmk I β j _ t (fun j' => colVec I j' i)]
    have hA1 : Matrix.mulVec (basisMat I β) x = gg_Nvec I := by
      rw [hxx, gg_A_Ainv I β hd]
    have hA2 : Matrix.mulVec (basisMat I β) U = colVec I j := gg_A_Ainv I β hd _
    have e1 := congrFun hA1 i
    have e2 := congrFun hA2 i
    simp only [Matrix.mulVec, dotProduct, basisMat, Matrix.of_apply, gg_Nvec] at e1 e2
    have : ∑ r, colVec I (β r) i * (x r - t * U r) =
        ∑ r, colVec I (β r) i * x r - t * ∑ r, colVec I (β r) i * U r := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro r _; ring
    rw [this, e1, e2]; ring
  · have hb : cost I (basicSol I β) = ∑ r, costRow I β r * x r := by
      unfold cost basicSol
      rw [gg_sum_basic I β _ (colCost I)]
      rfl
    have hz : cost I (zmk I β j (fun r => x r - t * U r) t) =
        ∑ r, costRow I β r * (x r - t * U r) + colCost I j * t :=
      sum_zmk I β j _ t (colCost I)
    rw [hz, hb]
    have : ∑ r, costRow I β r * (x r - t * U r) =
        ∑ r, costRow I β r * x r - t * ∑ r, costRow I β r * U r := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro r _; ring
    rw [this]
    nlinarith


theorem gg_pricing_4_5 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (j : Col I) (hj : j ∉ Set.range β) (U : Fin m → ℝ)
    (hU : Matrix.mulVec (basisMat I β) U = colVec I j) :
    (Improves I β j → colCost I j < ∑ r, costRow I β r * U r) ∧
    (IsNondegenerate I β →
      colCost I j < ∑ r, costRow I β r * U r → Improves I β j) := by
  have hd := hβ.1
  have hU' : U = Matrix.mulVec (basisMat I β)⁻¹ (colVec I j) := by
    rw [← hU, gg_Ainv_A I β hd]
  have hsum : ∑ r, costRow I β r * U r = ∑ k, mult I β k * colVec I j k := by
    rw [gg_mult_dot I β hd, hU']
  rw [hsum]
  exact ⟨fun h => (gg_crit1 I β hβ j h).2, fun hnd hc => gg_crit2 I β hβ hnd j hj hc⟩

theorem gg_step3 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (i : Fin m) (hi : Sum.inr i ∉ Set.range β) :
    (Improves I β (Sum.inr i) → mult I β i < 0) ∧
    (IsNondegenerate I β → mult I β i < 0 → Improves I β (Sum.inr i)) := by
  have hsum : ∑ k, mult I β k * colVec I (Sum.inr i) k = - mult I β i := by
    simp [colVec]
  have hc : colCost I (Sum.inr i : Col I) = 0 := rfl
  constructor
  · intro h
    have := (gg_crit1 I β hβ _ h).2
    rw [hsum, hc] at this; linarith
  · intro hnd hneg
    apply gg_crit2 I β hβ hnd _ hi
    rw [hsum, hc]; linarith

theorem gg_pricing_6_7 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β) (j : Fin k) :
    ((∃ p : Activity I, p.1.1 = j ∧ Improves I β (Sum.inl p)) →
      ∃ a : Fin m → ℕ, patLen I a ≤ I.L j ∧
        I.c j < ∑ i, mult I β i * (a i : ℝ)) ∧
    (IsNondegenerate I β →
      (∃ a : Fin m → ℕ, patLen I a ≤ I.L j ∧
        I.c j < ∑ i, mult I β i * (a i : ℝ)) →
      ∃ p : Activity I, p.1.1 = j ∧ Improves I β (Sum.inl p)) := by
  constructor
  · rintro ⟨⟨⟨j', a⟩, hp⟩, hj, himp⟩
    simp only at hj
    subst hj
    have := (gg_crit1 I β hβ _ himp).2
    exact ⟨a, hp, by simpa [colVec, colCost] using this⟩
  · intro hnd ⟨a, ha, hlt⟩
    refine ⟨⟨(j, a), ha⟩, rfl, ?_⟩
    have hnb : (Sum.inl (⟨(j, a), ha⟩ : Activity I) : Col I) ∉ Set.range β := by
      rintro ⟨r0, hr0⟩
      have := gg_basic_price I β hβ.1 r0
      rw [hr0] at this
      have h2 : ∑ k, mult I β k * colVec I (Sum.inl (⟨(j, a), ha⟩ : Activity I)) k =
          ∑ i, mult I β i * (a i : ℝ) := by simp [colVec]
      rw [h2] at this
      have h3 : colCost I (Sum.inl (⟨(j, a), ha⟩ : Activity I)) = I.c j := rfl
      rw [h3] at this
      linarith
    apply gg_crit2 I β hβ hnd _ hnb
    have h2 : ∑ k, mult I β k * colVec I (Sum.inl (⟨(j, a), ha⟩ : Activity I)) k =
          ∑ i, mult I β i * (a i : ℝ) := by simp [colVec]
    rw [h2]; exact hlt

theorem gg_step4 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (h3 : ∀ i, Sum.inr i ∉ Set.range β → 0 ≤ mult I β i)
    (h4 : ∀ j : Fin k, ¬ ∃ a : Fin m → ℕ,
      patLen I a ≤ I.L j ∧ I.c j < ∑ i, mult I β i * (a i : ℝ)) :
    Feasible I (basicSol I β) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    ∀ z : Col I →₀ ℝ, Feasible I z → Nbar I β (Sum.inl ()) ≤ cost I z := by
  have hd := hβ.1
  refine ⟨⟨?_, gg_cons_basic I β hd⟩, gg_cost_basic I β hd, ?_⟩
  · intro j'
    unfold basicSol
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_nonneg; intro r _
    rw [Finsupp.single_apply]; split_ifs
    · exact hβ.2 r
    · exact le_rfl
  · intro z hz
    -- dual feasibility of the multipliers
    have hdual : ∀ j : Col I, ∑ k, mult I β k * colVec I j k ≤ colCost I j := by
      intro j
      by_cases hj : j ∈ Set.range β
      · obtain ⟨r, rfl⟩ := hj
        exact (gg_basic_price I β hd r).le
      · rcases j with ⟨⟨j', a⟩, hp⟩ | i
        · have := h4 j'
          push_neg at this
          have h := this a hp
          simpa [colVec, colCost] using h
        · have := h3 i hj
          simp [colVec, colCost]
          linarith
    rw [gg_nbar_inl I β hd]
    have hcost : cost I z ≥ z.sum (fun j v => (∑ k, mult I β k * colVec I j k) * v) := by
      unfold cost Finsupp.sum
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_right (hdual j) (hz.1 j)
    have heq : z.sum (fun j v => (∑ k, mult I β k * colVec I j k) * v) =
        ∑ i, mult I β i * (I.N i : ℝ) := by
      unfold Finsupp.sum
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [← hz.2 i]
      unfold Finsupp.sum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring
    linarith

end LA
end GilmoreGomory61.CuttingStock

open GilmoreGomory61.CuttingStock


theorem solution {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (i : Fin m) (hi : Sum.inr i ∉ Set.range β) :
    (Improves I β (Sum.inr i) → mult I β i < 0) ∧
    (IsNondegenerate I β → mult I β i < 0 → Improves I β (Sum.inr i)) := by
  exact gg_step3 I β hβ i hi
