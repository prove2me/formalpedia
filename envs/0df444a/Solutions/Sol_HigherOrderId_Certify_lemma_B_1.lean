-- Prove2me | solution 1 for HigherOrderId.Certify.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:19:44.85818+00:00
-- url     : https://prove2.me/submissions/c487e280-e4c1-4ae8-a324-9b5bb575655f

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Release
import Definitions.Def_HigherOrderId_Certify_Fisher

section
open Matrix

namespace HigherOrderId.Certify.Dev.B1
open HigherOrderId.Certify

lemma sum_g (d E : ℕ) (D : Design d E) (h : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (hcent : ∑ e, D.x e = 0) (i : Fin d) :
    ∑ e, (h i + (H *ᵥ D.x e) i) = (E : ℝ) * h i := by
  have h1 : ∑ e, (H *ᵥ D.x e) i = 0 := by
    have : ∑ e, (H *ᵥ D.x e) i = (H *ᵥ (∑ e, D.x e)) i := by
      rw [Matrix.mulVec_sum]; simp [Finset.sum_apply]
    rw [this, hcent]; simp
  rw [Finset.sum_add_distrib, h1]; simp

lemma jensen (d E : ℕ) (D : Design d E) (h : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ)
    (hcent : ∑ e, D.x e = 0) :
    (E : ℝ) * ∑ i, h i ^ 2 ≤ ∑ e, ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2 := by
  have key : 0 ≤ ∑ e, ∑ i, ((h i + (H *ᵥ D.x e) i) - h i) ^ 2 := by positivity
  have exp : ∑ e, ∑ i, ((h i + (H *ᵥ D.x e) i) - h i) ^ 2 =
      ∑ e, ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2 - (E : ℝ) * ∑ i, h i ^ 2 := by
    have : ∀ e, ∑ i, ((h i + (H *ᵥ D.x e) i) - h i) ^ 2 =
        ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2 - 2 * ∑ i, h i * (h i + (H *ᵥ D.x e) i) + ∑ i, h i ^ 2 := by
      intro e; rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2 : ∑ e, 2 * ∑ i, h i * (h i + (H *ᵥ D.x e) i) = 2 * (E : ℝ) * ∑ i, h i ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm (f := fun e i => h i * _)]
      · have : ∑ i, ∑ e, h i * (h i + (H *ᵥ D.x e) i) = ∑ i, (E : ℝ) * h i ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.mul_sum, sum_g d E D h H hcent i]; ring
        rw [this, ← Finset.mul_sum]; ring
    rw [h2]; simp; ring
  linarith

lemma val_bound (d : ℕ) (x h g : Fin d → ℝ) (α : ℝ) (hx : Real.sqrt (∑ i, x i ^ 2) ≤ α)
    (v : ℝ) (hv : v = (1/2) * (x ⬝ᵥ (h + g))) :
    v ^ 2 ≤ (α ^ 2 / 2) * (∑ i, h i ^ 2 + ∑ i, g i ^ 2) := by
  have hxs : ∑ i, x i ^ 2 ≤ α ^ 2 := by
    have h0 : 0 ≤ Real.sqrt (∑ i, x i ^ 2) := Real.sqrt_nonneg _
    have := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => sq_nonneg (x i)))
    nlinarith
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (h + g)
  have hdot : x ⬝ᵥ (h + g) = ∑ i, x i * (h + g) i := rfl
  have h2 : ∑ i, (h + g) i ^ 2 ≤ 2 * (∑ i, h i ^ 2 + ∑ i, g i ^ 2) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _; simp only [Pi.add_apply]; nlinarith [sq_nonneg (h i - g i)]
  have hnn : 0 ≤ ∑ i, (h + g) i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnn2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [hv, hdot]
  calc (1/2 * ∑ i, x i * (h + g) i) ^ 2 = (1/4) * (∑ i, x i * (h + g) i) ^ 2 := by ring
    _ ≤ (1/4) * ((∑ i, x i ^ 2) * ∑ i, (h + g) i ^ 2) := by linarith
    _ ≤ (1/4) * (α ^ 2 * (2 * (∑ i, h i ^ 2 + ∑ i, g i ^ 2))) := by
        have := mul_le_mul hxs h2 hnn (sq_nonneg α); linarith
    _ = _ := by ring

theorem chk_lemma_B_1_core (d E : ℕ) (D : Design d E) (α σ : ℝ) (hd : 10 ≤ d) (hα0 : 0 < α)
    (hα1 : α ≤ 1 / 2) (hσ : 0 < σ) (hcent : ∑ e, D.x e = 0)
    (hbal : ∀ e e', D.n e = D.n e') (hpos : ∀ e, 1 ≤ D.n e)
    (hnorm : ∀ e, Real.sqrt (∑ i, D.x e i ^ 2) ≤ α)
    (h : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (hH : IsSymZeroDiag H) :
    gradFisher D σ h H ≤ fullFisher D σ h H ∧
    fullFisher D σ h H ≤ (1 + 2 * α ^ 2) * gradFisher D σ h H ∧
    (1 + 2 * α ^ 2) * gradFisher D σ h H ≤ (3 / 2) * gradFisher D σ h H := by
  have hcnn : ∀ e, 0 ≤ ((D.n e : ℝ) / σ ^ 2) := fun e => by positivity
  have hG : 0 ≤ gradFisher D σ h H :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hcnn e) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  have hV : 0 ≤ valueFisher D σ h H :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hcnn e) (sq_nonneg _))
  refine ⟨by unfold fullFisher; linarith, ?_, ?_⟩
  · unfold fullFisher
    suffices valueFisher D σ h H ≤ α ^ 2 * gradFisher D σ h H by nlinarith [sq_nonneg α]
    by_cases hE : Nonempty (Fin E)
    · obtain ⟨e0⟩ := hE
      set c : ℝ := (D.n e0 : ℝ) / σ ^ 2 with hc
      have hn : ∀ e, ((D.n e : ℝ) / σ ^ 2) = c := fun e => by rw [hc, hbal e e0]
      unfold valueFisher gradFisher
      simp_rw [hn]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hc0 : 0 ≤ c := hcnn e0
      have hjen := jensen d E D h H hcent
      have per : ∀ e, (h ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (H *ᵥ D.x e))) ^ 2 ≤
          (α ^ 2 / 2) * (∑ i, h i ^ 2 + ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2) := by
        intro e
        apply val_bound d (D.x e) h (fun i => h i + (H *ᵥ D.x e) i) α (hnorm e)
        have hh : h ⬝ᵥ D.x e = D.x e ⬝ᵥ h := dotProduct_comm _ _
        have hxh : D.x e ⬝ᵥ (h + fun i => h i + (H *ᵥ D.x e) i) =
            2 * (D.x e ⬝ᵥ h) + D.x e ⬝ᵥ (H *ᵥ D.x e) := by
          have : (h + fun i => h i + (H *ᵥ D.x e) i) = (2:ℝ) • h + H *ᵥ D.x e := by
            ext i; simp; ring
          rw [this, dotProduct_add, dotProduct_smul]; simp
        rw [hxh, hh]; ring
      have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => per e)
      rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have : c * ∑ e, (h ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (H *ᵥ D.x e))) ^ 2 ≤
          c * ((α ^ 2 / 2) * ((E:ℝ) * ∑ i, h i ^ 2 + ∑ e, ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum hc0
      have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
      nlinarith [mul_le_mul_of_nonneg_left hjen (mul_nonneg hc0 hα2)]
    · have : IsEmpty (Fin E) := not_nonempty_iff.mp hE
      simp [valueFisher, gradFisher]
  · have h4 : α ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hG]

end HigherOrderId.Certify.Dev.B1

namespace HigherOrderId.Certify

theorem chk_lemma_B_1 (d E : ℕ) (D : Design d E) (α σ : ℝ) (hd : 10 ≤ d) (hα0 : 0 < α)
    (hα1 : α ≤ 1 / 2) (hσ : 0 < σ) (hcent : ∑ e, D.x e = 0)
    (hbal : ∀ e e', D.n e = D.n e') (hpos : ∀ e, 1 ≤ D.n e)
    (hnorm : ∀ e, Real.sqrt (∑ i, D.x e i ^ 2) ≤ α)
    (h : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (hH : IsSymZeroDiag H) :
    gradFisher D σ h H ≤ fullFisher D σ h H ∧
    fullFisher D σ h H ≤ (1 + 2 * α ^ 2) * gradFisher D σ h H ∧
    (1 + 2 * α ^ 2) * gradFisher D σ h H ≤ (3 / 2) * gradFisher D σ h H :=
  Dev.B1.chk_lemma_B_1_core d E D α σ hd hα0 hα1 hσ hcent hbal hpos hnorm h H hH

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_lemma_B_1 := @HigherOrderId.Certify.chk_lemma_B_1
