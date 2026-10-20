-- Prove2me | solution 1 for OAI.Cotype.averaged_projection_power_bound_of_sign_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:49:38.084933+00:00
-- url     : https://prove2.me/submissions/c0da9d6a-8129-4046-ac9e-73bd9a4d3bbd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionAverages.lean:L51-L75
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.averaged_projection_power_bound_of_sign_deficit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Theorems.Thm_OAI_Cotype_exists_sign_of_radius
import Theorems.Thm_OAI_Cotype_projectionComplement_expansion
import Theorems.Thm_OAI_Cotype_projectionSubset_union

-- ---- from OAI.Analysis.Cotype.ProjectionProducts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x : X) : ‖projectionProduct P x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih => exact (h 0 _).trans (ih _ (fun i => h i.succ))

theorem projectionSubset_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (ε : Cube n) (x : X) :
    ‖projectionSubset P ε x‖ ≤ ‖x‖ := by
  apply projectionProduct_norm_apply
  intro i z
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp
  · exact h i z

theorem projectionSubset_singleton {n : ℕ} (P : Fin n → X →L[ℝ] X) (i : Fin n) :
    projectionSubset P (fun j => decide (j = i)) = P i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [projectionSubset, projectionProduct, projectionProduct_one]
    · have hi0 : (0 : Fin (n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
      simpa [projectionSubset, projectionProduct, hi0] using
        ih (fun j => P j.succ) i

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionDeficit ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_norming_sum_deficit {ι : Type*} [Fintype ι]
    (v : ι → X) {R : ℝ} (_hR : 0 ≤ R) (hv : ∀ i, ‖v i‖ ≤ R) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ ∀ i,
      R - ((Fintype.card ι : ℝ)*R-‖∑ j, v j‖) ≤ φ (v i) := by
  classical
  obtain ⟨φ,hφ,he⟩ := exists_dual_vector'' ℝ (∑ j, v j)
  have he' : φ (∑ j, v j) = ‖∑ j, v j‖ := he
  have hb i : φ (v i) ≤ R := by
    apply (le_abs_self _).trans
    exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans (hv i))
  refine ⟨φ,hφ,fun i => ?_⟩
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hb j))
    (Finset.mem_univ i)
  have hs : (∑ j, (R-φ (v j))) = (Fintype.card ι : ℝ)*R-‖∑ j, v j‖ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← map_sum, he']
  rw [hs] at hi
  linarith

theorem abs_prod_sign {n : ℕ} (ε : Cube n) : |∏ i, sign (ε i)| = 1 := by
  rw [Finset.abs_prod]
  have hs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
  simp_rw [hs]
  simp

theorem prod_sign_union_singleton {n : ℕ} (ε : Cube n) (i : Fin n) :
    (∏ j, sign ((!ε j) || decide (j = i))) =
      (∏ j, sign (!ε j)) * sign (ε i) := by
  classical
  have he : (∏ j ∈ Finset.univ.erase i, sign ((!ε j) || decide (j = i))) =
      ∏ j ∈ Finset.univ.erase i, sign (!ε j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), he,
    ← Finset.prod_erase_mul _ (fun j => sign (!ε j)) (Finset.mem_univ i)]
  simp only [decide_true, Bool.or_true, sign_true, sign_not]
  cases ε i <;> norm_num

theorem projection_sign_sum_lower {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hn : ∀ i x, ‖P i x‖ ≤ ‖x‖) (y : X) (ε : Cube n) :
    (n : ℝ)*(‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) ≤
      ‖rademacherSum X (fun i => P i y) ε‖ := by
  classical
  let v : Cube n → X := fun η => (∏ i, sign (η i)) • projectionSubset P η y
  have hv η : ‖v η‖ ≤ ‖y‖ := by
    simpa only [v, norm_smul, Real.norm_eq_abs, abs_prod_sign, one_mul] using
      projectionSubset_norm_apply P hn η y
  have hsum : (∑ η, v η) = projectionProduct (fun i => 1-P i) y := by
    rw [projectionComplement_expansion]
    simp [v]
  obtain ⟨φ,hφ,hφv⟩ := exists_norming_sum_deficit v (norm_nonneg y) hv
  have hcard : (Fintype.card (Cube n) : ℝ) = (2 : ℝ)^n := by
    simp [Cube]
  rw [hcard, hsum] at hφv
  let B : Cube n := fun i => !ε i
  let a : ℝ := ∏ i, sign (B i)
  let z : X := rademacherSum X (fun i => P i y) ε
  have hi i : a * φ (projectionSubset P B (sign (ε i) • P i y)) =
      φ (v (fun j => B j || decide (j = i))) := by
    have hm := projectionSubset_union P hp hc B (fun j => decide (j = i))
    rw [projectionSubset_singleton] at hm
    have hmap : projectionSubset P B (P i y) =
        projectionSubset P (fun j => B j || decide (j = i)) y := by
      exact congrArg (fun T : X →L[ℝ] X => T y) hm
    simp only [map_smul, smul_eq_mul, hmap, v]
    rw [prod_sign_union_singleton ε i]
    dsimp [a, B]
    ring
  have hlow : (n : ℝ)*(‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) ≤
      a * φ (projectionSubset P B z) := by
    dsimp [z, rademacherSum]
    simp only [map_sum, Finset.mul_sum]
    calc
      _ = ∑ _i : Fin n, (‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [hi]; exact hφv _)
  apply hlow.trans
  calc
    _ ≤ |a * φ (projectionSubset P B z)| := le_abs_self _
    _ = |φ (projectionSubset P B z)| := by rw [abs_mul, show |a|=1 from abs_prod_sign B, one_mul]
    _ ≤ ‖projectionSubset P B z‖ := (φ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hφ)
    _ ≤ ‖z‖ := projectionSubset_norm_apply P hn B z

theorem projection_complement_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i x, ‖P i x‖ ≤ ‖x‖) (y : X) :
    ‖projectionProduct (fun i => 1-P i) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  obtain ⟨ε,hε⟩ := exists_sign_of_radius h (norm_nonneg y) (fun i => P i y) (fun i => hP i y)
  have hl := projection_sign_sum_lower P hp hc hP y ε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ)*(δ/(n : ℝ)) = δ := mul_div_cancel₀ δ (ne_of_gt hnR)
  have he' : (n : ℝ)*(δ/(n : ℝ))*‖y‖ = δ*‖y‖ := by rw [he]
  apply (mul_le_mul_iff_right₀ hnR).mp
  nlinarith [he']

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionAverages ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_const (T : X →L[ℝ] X) (n : ℕ) :
    projectionProduct (fun _ : Fin n => T) = T^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [projectionProduct, ih, pow_succ']

theorem projection_weight_total {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    (∑ ω : Fin n → Ω, ∏ i, w i (ω i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp_rw [hw]
  simp

theorem averaged_projection_power_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (P : Ω → X →L[ℝ] X)
    (hp : ∀ a, P a * P a = P a) (hc : ∀ a b, Commute (P a) (P b))
    (hP : ∀ a x, ‖P a x‖ ≤ ‖x‖) (y : X) :
    ‖((1-∑ a, w a • P a)^n) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  classical
  have he : (1-∑ a, w a • P a) = ∑ a, w a • (1-P a) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  rw [he, ← projectionProduct_const, projectionProduct_weighted_sum]
  simp only [sum_apply, smul_apply]
  calc
    _ ≤ ∑ ω : Fin n → Ω, ‖(∏ i, w (ω i)) • projectionProduct (fun i => 1-P (ω i)) y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ω : Fin n → Ω, (∏ i, w (ω i))*(((2 : ℝ)^n-δ/n)*‖y‖) := by
      apply Finset.sum_le_sum
      intro ω _
      have hwω : 0 ≤ ∏ i : Fin n, w (ω i) := Finset.prod_nonneg (fun i _ => hw (ω i))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwω]
      apply mul_le_mul_of_nonneg_left _ hwω
      exact projection_complement_bound_of_sign_deficit hn h (fun i => P (ω i))
        (fun i => hp (ω i)) (fun i j => hc (ω i) (ω j)) (fun i => hP (ω i)) y
    _ = _ := by rw [← Finset.sum_mul, projection_weight_total (fun _ => w) (fun _ => hw1), one_mul]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.averaged_projection_power_bound_of_sign_deficit := @_root_.OAI.Cotype.averaged_projection_power_bound_of_sign_deficit
