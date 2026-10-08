-- Prove2me | solution 1 for GilmoreGomory61.CuttingStock.bordered_inverse_first_row
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:29:55.018553+00:00
-- url     : https://prove2.me/submissions/e77ae841-04fa-4f03-aa31-2c48a5e08e66

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

end LA
end GilmoreGomory61.CuttingStock

open GilmoreGomory61.CuttingStock


theorem solution {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsUnit (basisMat I β).det) :
    (bordered I β)⁻¹ =
      Matrix.fromBlocks 1
        (Matrix.of fun _ r => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
        0 (basisMat I β)⁻¹ ∧
    mult I β = Matrix.vecMul (costRow I β) (basisMat I β)⁻¹ ∧
    (∀ j : Col I, priceOut I β j =
      (∑ i, mult I β i * colVec I j i) - colCost I j) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    (∀ i, ((basicSol I β).sum fun j v => colVec I j i * v) = (I.N i : ℝ)) := by
  exact gg_first_row I β hβ
