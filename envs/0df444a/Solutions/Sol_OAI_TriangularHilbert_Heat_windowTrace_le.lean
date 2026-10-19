-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.windowTrace_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:57:25.685709+00:00
-- url     : https://prove2.me/submissions/60c95f7d-e94a-48e2-a676-0c2f6cbf445b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedTraceOrder.lean:L115-L133
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.windowTrace_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_le_of_le_smul
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_starInsert_eq_insertRow
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sylv_solvable_inserted_gram
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_vertexRoot_insert
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_weightedGram_rowBare_congr

-- ---- from OAI.Analysis.TriangularHilbert.SignedWindowScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_dilation {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (t : ℝ) :
    density (q*s) t = (Real.sqrt s)⁻¹ * density q (t/Real.sqrt s) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  have he : -(t/Real.sqrt s)^2/(2*q) = -t^2/(2*(q*s)) := by
    field_simp
    nlinarith [hsq]
  unfold density
  rw [show 2*Real.pi*(q*s)=s*(2*Real.pi*q) by ring,Real.sqrt_mul hs.le,he]
  simp only [mul_inv_rev]
  ring

lemma density_one_lambda (z : ℝ) :
    density 1 z = Real.sqrt (11/10) * Real.exp (-z^2/22) * density (11/10) z := by
  have hr : Real.sqrt (11/10) ≠ 0 := by positivity
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hn : 2*Real.pi*(11/10) = (11/10)*(2*Real.pi) := by ring
  unfold density
  rw [hn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 11/10)]
  simp only [mul_one,mul_inv_rev]
  have he : -z^2/22 + -z^2/(2*(11/10)) = -z^2/(2*1) := by ring
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-z^2/22 + -z^2/(2*(11/10))) := by rw [he]; simp
    _ = _ := by rw [Real.exp_add]; field_simp

lemma density_lambda_relation {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t = Real.sqrt (11/10) * Real.exp (-(t/Real.sqrt s)^2/22) * density ((11/10)*s) t := by
  have h1 := density_dilation hs (by norm_num : (0:ℝ)<1) t
  rw [one_mul] at h1
  rw [h1,density_dilation hs (by norm_num : (0:ℝ)<11/10),density_one_lambda]
  ring

lemma density_le_lambda {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t ≤ Real.sqrt (11/10)*density ((11/10)*s) t := by
  rw [density_lambda_relation hs t]
  have he : Real.exp (-(t/Real.sqrt s)^2/22) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)) (density_nonneg (by positivity) t)

lemma windowRatio_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    windowRatio s t = Real.sqrt (11/10)*(t/Real.sqrt s)*Real.exp (-(t/Real.sqrt s)^2/22) := by
  unfold windowRatio oddWindow
  rw [density_lambda_relation hs t]
  have hn : density ((11/10)*s) t ≠ 0 := (density_pos (by positivity) t).ne'
  rw [← mul_assoc, mul_div_cancel_right₀ _ hn]
  ring

lemma abs_mul_exp_square_le (z : ℝ) : |z| *Real.exp (-z^2/22) ≤ 22 := by
  have h := Real.add_one_le_exp (z^2/22)
  have hp := Real.exp_pos (-z^2/22)
  have ha : |z| ≤ 22*(z^2/22+1) := by nlinarith [sq_nonneg (|z|-1),sq_abs z]
  have he : Real.exp (z^2/22) * Real.exp (-z^2/22) = 1 := by rw [← Real.exp_add,show z^2/22 + -z^2/22 = 0 by ring,Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right h hp.le
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_right ha hp.le
  nlinarith

lemma abs_windowRatio_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |windowRatio s t| ≤ 44 := by
  rw [windowRatio_eq hs t,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos (Real.exp_pos _)]
  have h := abs_mul_exp_square_le (t/Real.sqrt s)
  have hr : Real.sqrt (11/10) ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hn := Real.sqrt_nonneg (11/10)
  nlinarith

lemma oddWindow_score {s : ℝ} (hs : 0 < s) (u p : ℝ) :
    oddWindow s (u-p) = Real.sqrt s*score u p s*density s (u-p) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  unfold oddWindow score
  congr 1
  field_simp
  rw [hsq]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

theorem cyclic_sum_insert {ι : Type uι} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (f : ι → ι → ι → ℂ)
    (hf : ∀ i j k, f i j k = f j k i) :
    (∑ i ∈ insert a s, ∑ j ∈ insert a s, ∑ k ∈ insert a s, f i j k) =
      f a a a + 3 * (∑ j ∈ s, f a a j) +
        3 * (∑ j ∈ s, ∑ k ∈ s, f a j k) +
        (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k) := by
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  have h1 : (∑ i ∈ s, f a i a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hf a i a).trans (hf i a a)
  have h2 : (∑ i ∈ s, f i a a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hf i a a
  have h3 : (∑ i ∈ s, ∑ j ∈ s, f i a j) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    simp_rw [hf _ a _]
    exact Finset.sum_comm
  have h4 : (∑ i ∈ s, ∑ j ∈ s, f i j a) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hf i j a).trans (hf j a i)
  rw [h1, h2, h3, h4]
  ring

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

theorem norm_quad_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖∑ j, ∑ k, star (x j) * D j k * x k‖ ≤
      ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hform : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ⟪v, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v⟫_ℂ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec,
      dotProduct, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, v]
  rw [hform]
  calc
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := by
      gcongr
      exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
    _ = ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq v]
      ring

theorem column_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (i : ι) :
    (∑ j, ‖D j i‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := EuclideanSpace.single i 1
  have hn : ‖v‖ = 1 := by simp [v]
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
  rw [hn, Matrix.l2_opNorm_toEuclideanCLM, mul_one] at h
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h
  simpa [EuclideanSpace.norm_sq_eq, v, Matrix.mulVec, dotProduct] using hs

theorem row_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i : ι) :
    (∑ j, ‖D i j‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  convert column_sq_sum_le D i using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hD.apply i j, norm_star]

theorem hermitian_entry_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i j : ι) :
    ‖D i j‖ ≤ ‖D‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖D i k‖)
    (Finset.mem_univ j)).trans (row_sq_sum_le D hD i)

theorem norm_cyclic_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i‖ ≤
      ‖D‖ * ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
  let x : ι → ℂ := fun j => if j ∈ s then (m j : ℂ) * D j i else 0
  have hf' (j k : ι) : star (x j) * D j k * x k =
      if j ∈ s then if k ∈ s then
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i else 0 else 0 := by
    by_cases hj : j ∈ s <;> by_cases hk : k ∈ s
    all_goals simp [x, hj, hk, hD.apply, mul_comm, mul_left_comm]
  have hf : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i := by
    simp_rw [hf']
    simp [Finset.sum_ite_mem]
  have hn' (j : ι) : ‖x j‖ ^ 2 =
      if j ∈ s then (m j) ^ 2 * ‖D i j‖ ^ 2 else 0 := by
    by_cases hj : j ∈ s
    · simp [x, hj, mul_pow, ← hD.apply i j]
    · simp [x, hj]
  have hn : (∑ j, ‖x j‖ ^ 2) = ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
    simp_rw [hn']
    simp [Finset.sum_ite_mem]
  simpa only [hf, hn] using norm_quad_sum_le D x

theorem norm_weighted_row_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ ≤
      Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
  have hs : (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg s.subset_univ
      (fun j _ _ => sq_nonneg ‖D i j‖)).trans (row_sq_sum_le D hD i)
  have hr : Real.sqrt (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖ :=
    (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hs⟩
  calc
    _ ≤ ∑ j ∈ s, ‖(m j : ℂ) * D i j * D j i‖ := norm_sum_le _ _
    _ = ∑ j ∈ s, (|m j| * ‖D i j‖) * ‖D i j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [← hD.apply i j]
    _ ≤ Real.sqrt (∑ j ∈ s, (|m j| * ‖D i j‖)^2) *
        Real.sqrt (∑ j ∈ s, ‖D i j‖^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
      simp only [mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)

theorem norm_twice_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖(m i : ℂ)^2 * D i i * (∑ j ∈ s, (m j : ℂ) * D i j * D j i)‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  let B := ∑ j ∈ s, (m j)^2 * ‖D i j‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYoung : |m i|^2 * ‖D i i‖ * Real.sqrt B ≤
      (|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2 := by
    have hsq := mul_nonneg (abs_nonneg (m i))
      (sq_nonneg (|m i| * ‖D i i‖ - Real.sqrt B))
    have hr := congrArg (fun z : ℝ => |m i| * z) (Real.sq_sqrt hB)
    nlinarith
  calc
    _ = |m i|^2 * ‖D i i‖ * ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ := by
      simp [norm_pow]
    _ ≤ |m i|^2 * ‖D i i‖ * (Real.sqrt B * ‖D‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_row_le D hD m i s) (by positivity)
    _ = ‖D‖ * (|m i|^2 * ‖D i i‖ * Real.sqrt B) := by ring
    _ ≤ ‖D‖ * ((|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2) :=
      mul_le_mul_of_nonneg_left hYoung (norm_nonneg _)
    _ = _ := by dsimp [B]; ring

theorem spectralWeight_symm {ι : Type uι} (D : Matrix ι ι ℂ)
    (hD : D.IsHermitian) (m : ι → ℝ) (i j : ι) :
    spectralWeight D m i j = spectralWeight D m j i := by
  unfold spectralWeight
  rw [← hD.apply i j, norm_star]
  ring

theorem spectralWeight_diag {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i : ι) :
    spectralWeight D m i i = |m i|^3 * ‖D i i‖^2 / 2 := by
  unfold spectralWeight
  by_cases h : m i = 0
  · simp [h]
  · have h' : |m i| ≠ 0 := abs_ne_zero.mpr h
    field_simp
    ring

theorem spectralWeight_pair_ge {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ)
    (i j : ι) (hij : |m j| ≤ |m i|) :
    |m i| * (m j)^2 * ‖D i j‖^2 ≤ 2 * spectralWeight D m i j := by
  unfold spectralWeight
  by_cases hi : m i = 0
  · simp [hi]
  · have hp : 0 < |m i| + |m j| := add_pos_of_pos_of_nonneg (abs_pos.mpr hi) (abs_nonneg _)
    have hbase : |m i| * |m j|^2 ≤ 2 * (|m i|^2 * |m j|^2 / (|m i| + |m j|)) := by
      rw [← mul_div_assoc, le_div_iff₀ hp]
      have hmul := mul_nonneg (mul_nonneg (abs_nonneg (m i)) (sq_nonneg |m j|))
        (sub_nonneg.mpr hij)
      nlinarith
    simpa only [sq_abs, mul_assoc] using mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖D i j‖)

theorem cubicTerm_cyclic {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) :
    cubicTerm D m i j k = cubicTerm D m j k i := by unfold cubicTerm; ring

theorem norm_cubicTerm_diag_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) :
    ‖cubicTerm D m i i i‖ ≤ ‖D‖ * (|m i|^3 * ‖D i i‖^2) := by
  calc
    _ = (|m i|^3 * ‖D i i‖^2) * ‖D i i‖ := by
      simp only [cubicTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ (|m i|^3 * ‖D i i‖^2) * ‖D‖ := by
      gcongr
      exact hermitian_entry_le D hD i i
    _ = _ := by ring

theorem norm_cubicTerm_twice_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, cubicTerm D m i i j‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  convert norm_twice_tail_le D hD m i s using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold cubicTerm
  ring

theorem norm_cubicTerm_once_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      ‖D‖ * (|m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  have heq : (∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k) =
      (m i : ℂ) * (∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    unfold cubicTerm
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |m i| * (‖D‖ * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) :=
      mul_le_mul_of_nonneg_left (norm_cyclic_tail_le D hD m i s) (abs_nonneg _)
    _ = _ := by ring

theorem spectralWeight_insert_ge {ι : Type uι} [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (s : Finset ι) (a : ι) (ha : a ∉ s) (hmax : ∀ j ∈ s, |m j| ≤ |m a|) :
    |m a|^3 * ‖D a a‖^2 / 2 +
      |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 +
      (∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j) ≤
      ∑ i ∈ insert a s, ∑ j ∈ insert a s, spectralWeight D m i j := by
  have hrs : (∑ j ∈ s, spectralWeight D m j a) =
      ∑ j ∈ s, spectralWeight D m a j := by
    apply Finset.sum_congr rfl
    intro j _
    exact spectralWeight_symm D hD m j a
  have hp : |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 ≤
      2 * ∑ j ∈ s, spectralWeight D m a j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_assoc] using spectralWeight_pair_ge D m a j (hmax j hj)
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  rw [hrs, spectralWeight_diag]
  linarith

theorem norm_cubic_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (s : Finset ι) :
    ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      5 * ‖D‖ * ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j := by
  induction s using Finset.induction_on_max_value (fun i => |m i|) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [cyclic_sum_insert s a ha _ (cubicTerm_cyclic D m)]
    let A := |m a|^3 * ‖D a a‖^2
    let E := |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2
    let Q := ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hdiag := norm_cubicTerm_diag_le D hD m a
    have htwice := norm_cubicTerm_twice_le D hD m a s
    have honce := norm_cubicTerm_once_le D hD m a s
    calc
      _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j +
          3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := norm_add_le _ _
      _ ≤ (‖cubicTerm D m a a a‖ + 3 * ‖∑ j ∈ s, cubicTerm D m a a j‖ +
          3 * ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖) +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := by
        gcongr
        calc
          _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j‖ +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := norm_add_le _ _
          _ ≤ (‖cubicTerm D m a a a‖ + ‖3 * ∑ j ∈ s, cubicTerm D m a a j‖) +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := by
            gcongr
            exact norm_add_le _ _
          _ = _ := by simp
      _ ≤ (‖D‖ * A + 3 * (‖D‖ / 2 * (A + E)) + 3 * (‖D‖ * E)) +
          5 * ‖D‖ * Q := by
        exact add_le_add (add_le_add (add_le_add hdiag
          (mul_le_mul_of_nonneg_left htwice (by norm_num)))
          (mul_le_mul_of_nonneg_left honce (by norm_num))) ih
      _ ≤ 5 * ‖D‖ * (A / 2 + E + Q) := by
        nlinarith [mul_nonneg (norm_nonneg D) hE]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (spectralWeight_insert_ge D hD m s a ha hmax) (by positivity)

theorem trace_cube_mul_diagonal {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (m : ι → ℝ) :
    Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      ∑ i, ∑ j, ∑ k, cubicTerm D m i j k := by
  have expand (A : Matrix ι ι ℂ) :
      Matrix.trace (A^3) = ∑ i, ∑ j, ∑ k, A i j * (A j k * A k i) := by
    have hp : A^3 = A * (A * A) := by noncomm_ring
    rw [hp]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  rw [expand]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold cubicTerm
  ring

theorem norm_trace_cube_mul_diagonal_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) :
    ‖Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3)‖ ≤
      5 * ‖D‖ * ∑ i, ∑ j, spectralWeight D m i j := by
  rw [trace_cube_mul_diagonal]
  exact norm_cubic_sum_le D hD m Finset.univ

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem traceReal_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ traceReal A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

theorem penalty_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (X : Matrix ι ι ℂ) : 0 ≤ penalty A X := by
  simp only [penalty, hsReal, sylv, mul_add, traceReal_add]
  have h₁ := traceReal_nonneg (hA.conjTranspose_mul_mul_same X)
  have h₂ := traceReal_nonneg (hA.mul_mul_conjTranspose_same X)
  rw [Matrix.mul_assoc] at h₁
  rw [← Matrix.mul_assoc Xᴴ X A, traceReal_mul_cycle Xᴴ X A,
    traceReal_mul_cycle A Xᴴ X]
  exact add_nonneg h₁ h₂

theorem penalty_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    penalty A (X - Y) = penalty A X + penalty A Y - 2 * hsReal (sylv A Y) X := by
  simp only [penalty, sylv_sub_right, hsReal_sub_left, hsReal_sub_right]
  rw [hsReal_symm Y (sylv A X), ← hsReal_sylv_symm hA, hsReal_symm X (sylv A Y)]
  ring

theorem penalty_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (X : Matrix ι ι ℂ) :
    penalty A X ≤ penalty B X := by
  have h := penalty_nonneg hAB X
  simpa only [penalty, sylv_sub_left, hsReal_sub_right, sub_nonneg] using h

theorem variation_sylv {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    variation A (sylv A Y) X = penalty A Y - penalty A (X - Y) := by
  rw [variation, penalty_sub hA]
  ring

theorem variation_bddAbove {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : BddAbove (Set.range (variation A K)) := by
  obtain ⟨Y, rfl⟩ := hsol
  refine ⟨penalty A Y, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [variation_sylv hA.isHermitian]
  exact sub_le_self _ (penalty_nonneg hA _)

theorem rootCost_antitone {A B K : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    rootCost B K ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans
    (le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩)

theorem hsReal_eq_sum (X Y : Matrix ι ι ℂ) :
    hsReal X Y = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  simp only [hsReal, traceReal, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

variable [DecidableEq ι]

theorem rootCost_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (K : Matrix ι ι ℂ) (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    rootCost (Matrix.diagonal (fun i => (q i : ℂ))) K =
      (3 / 2 : ℝ) * ∑ i, ∑ j, ‖K i j‖^2 / (q i + q j) := by
  have hq' : (Matrix.diagonal (fun i => (q i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hq i))
  rw [rootCost_eq_of_solution hq' (diagonalSolution_solves q K hsupp), hsReal_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [diagonalSolution, ← mul_div_assoc, RCLike.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_re, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem hsReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X Y : Matrix ι ι ℂ) :
    hsReal (conjStarAlgAut ℂ _ U X) (conjStarAlgAut ℂ _ U Y) = hsReal X Y := by
  change traceReal (star (conjStarAlgAut ℂ _ U X) * conjStarAlgAut ℂ _ U Y) = _
  rw [← map_star, ← map_mul, traceReal_unitary_conj]
  rfl

theorem variation_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K X : Matrix ι ι ℂ) :
    variation (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K)
      (conjStarAlgAut ℂ _ U X) = variation A K X := by
  simp only [variation, penalty, sylv_unitary_conj, hsReal_unitary_conj]

theorem rootCost_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K : Matrix ι ι ℂ) :
    rootCost (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K) = rootCost A K := by
  unfold rootCost
  congr 2
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := (conjStarAlgAut ℂ _ U).surjective X
    exact ⟨Y, (variation_unitary_conj U A K Y).symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨conjStarAlgAut ℂ _ U X, variation_unitary_conj U A K X⟩

theorem hessianCost_antitone {P Q K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (hPQ : P ≤ Q) :
    hessianCost Q K ≤ hessianCost P K := by
  exact rootCost_antitone (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol (CFC.monotone_sqrt hPQ)

theorem hsReal_single (K : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    hsReal K (Matrix.single i j z) = (star (K i j) * z).re := by
  simp [hsReal_eq_sum, Matrix.single_apply, ite_and, apply_ite]

theorem sylv_diagonal_single (q : ι → ℝ) (i j : ι) (z : ℂ) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (Matrix.single i j z) =
      Matrix.single i j (((q i + q j : ℝ) : ℂ) * z) := by
  ext a b
  rw [sylv_diagonal_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b; simp
    · simp [hb]
  · simp [ha]

theorem sylv_solvable_diagonal_of_bddAbove (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hb : BddAbove (Set.range (variation (Matrix.diagonal (fun i => (q i : ℂ))) K))) :
    ∃ Y, sylv (Matrix.diagonal (fun i => (q i : ℂ))) Y = K := by
  refine ⟨diagonalSolution q K, diagonalSolution_solves q K ?_⟩
  intro i j hij
  by_contra hK
  obtain ⟨b, hb⟩ := hb
  let X := Matrix.single i j (K i j)
  have hzero : sylv (Matrix.diagonal (fun i => (q i : ℂ))) X = 0 := by
    simp [X, sylv_diagonal_single, hij]
  have hhs : hsReal K X = ‖K i j‖^2 := by
    rw [hsReal_single]
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖K i j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hK)
  let t : ℝ := b / (2 * ‖K i j‖^2) + 1
  have ht := hb (Set.mem_range_self (t • X))
  change variation _ K (t • X) ≤ b at ht
  simp only [variation, penalty, sylv_smul_right, hzero, smul_zero,
    hsReal_zero_right, sub_zero, hsReal_smul_right, hhs] at ht
  have hcalc : 2 * (t * ‖K i j‖^2) = b + 2 * ‖K i j‖^2 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  rw [hcalc] at ht
  linarith

theorem sylv_solvable_of_bddAbove {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hb : BddAbove (Set.range (variation A K))) : ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let K' := f K
  have hAd : f A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb' : BddAbove (Set.range (variation (f A) K')) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b, ?_⟩
    rintro _ ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := f.surjective X
    change variation (f A) (f K) (f Y) ≤ b
    exact (variation_unitary_conj (star U) A K Y) ▸ hb (Set.mem_range_self Y)
  rw [hAd] at hb'
  obtain ⟨Y, hY⟩ := sylv_solvable_diagonal_of_bddAbove _ K' hb'
  refine ⟨f.symm Y, ?_⟩
  apply f.injective
  change f (sylv A (f.symm Y)) = f K
  calc
    _ = sylv (f A) (f (f.symm Y)) := (sylv_unitary_conj (star U) A (f.symm Y)).symm
    _ = sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y := by
      rw [f.apply_symm_apply, hAd]
    _ = _ := hY

theorem sylv_solvable_mono {A B K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    ∃ Y, sylv B Y = K := by
  apply sylv_solvable_of_bddAbove hB
  obtain ⟨b, hb⟩ := variation_bddAbove hA hsol
  refine ⟨b, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans (hb (Set.mem_range_self X))

omit [DecidableEq ι] in
theorem rootCost_smul_direction {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (c : ℝ) :
    rootCost A (c • K) = c^2 * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hc : sylv A (c • Y) = c • K := by rw [sylv_smul_right, hY]
  rw [rootCost_eq_of_solution hA hc, rootCost_eq_of_solution hA hY,
    hsReal_smul_left, hsReal_smul_right]
  ring

omit [DecidableEq ι] in
theorem penalty_three_identity (A X Y Z : Matrix ι ι ℂ) :
    3 * (penalty A X + penalty A Y + penalty A Z) - penalty A (X + Y + Z) =
      penalty A (X - Y) + penalty A (Y - Z) + penalty A (Z - X) := by
  simp only [penalty, sylv_add_right, sylv_sub_right, hsReal_add_left,
    hsReal_add_right, hsReal_sub_left, hsReal_sub_right]
  ring

omit [DecidableEq ι] in
theorem rootCost_three_le {A K L M : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : ∃ X, sylv A X = K) (hL : ∃ Y, sylv A Y = L)
    (hM : ∃ Z, sylv A Z = M) :
    rootCost A (K + L + M) ≤ 3 * (rootCost A K + rootCost A L + rootCost A M) := by
  obtain ⟨X, rfl⟩ := hK
  obtain ⟨Y, rfl⟩ := hL
  obtain ⟨Z, rfl⟩ := hM
  have hall : sylv A (X + Y + Z) = sylv A X + sylv A Y + sylv A Z := by simp
  rw [rootCost_eq_of_solution hA hall, rootCost_eq_of_solution hA rfl,
    rootCost_eq_of_solution hA rfl, rootCost_eq_of_solution hA rfl]
  rw [← hall]
  have hc := penalty_three_identity A X Y Z
  have hn := add_nonneg (add_nonneg (penalty_nonneg hA (X - Y))
    (penalty_nonneg hA (Y - Z))) (penalty_nonneg hA (Z - X))
  rw [hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _,
    hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _]
  change (3 / 2 : ℝ) * penalty A (X + Y + Z) ≤
    3 * ((3 / 2 : ℝ) * penalty A X + (3 / 2 : ℝ) * penalty A Y +
      (3 / 2 : ℝ) * penalty A Z)
  linarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem trace_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    Matrix.trace (conjStarAlgAut ℂ _ U X) = Matrix.trace X := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem norm_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    ‖conjStarAlgAut ℂ _ U X‖ = ‖X‖ := by
  rw [conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem hermitian_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (conjStarAlgAut ℂ _ U X).IsHermitian := by
  change star (conjStarAlgAut ℂ _ U X) = conjStarAlgAut ℂ _ U X
  rw [← map_star]
  exact congrArg (conjStarAlgAut ℂ _ U) hX

theorem sqrt_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    CFC.sqrt (conjStarAlgAut ℂ _ U P) = conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
        (U : Matrix ι ι ℂ)).nonneg

theorem hessianCost_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (K : Matrix ι ι ℂ) :
    hessianCost (conjStarAlgAut ℂ _ U P) (conjStarAlgAut ℂ _ U K) =
      hessianCost P K := by
  simp only [hessianCost, sqrt_unitary_conj U hP, rootCost_unitary_conj]

theorem sqrt_diagonal_square (m : ι → ℝ) :
    CFC.sqrt (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ))) =
      Matrix.diagonal (fun i => ((|m i| : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    change ((|m i| : ℝ) : ℂ) * ((|m i| : ℝ) : ℂ) = (m i : ℂ) * (m i : ℂ)
    exact_mod_cast (show |m i| * |m i| = m i * m i by nlinarith [sq_abs (m i)])
  · exact (Matrix.PosSemidef.diagonal
      (fun i => RCLike.ofReal_nonneg.mpr (abs_nonneg (m i)))).nonneg

theorem hessianCost_diagonal_square (m : ι → ℝ) (D : Matrix ι ι ℂ) :
    hessianCost (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ)))
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
       Matrix.diagonal (fun i => (m i : ℂ))) =
      (3 / 2 : ℝ) * ∑ i, ∑ j, spectralWeight D m i j := by
  unfold hessianCost
  rw [sqrt_diagonal_square]
  have hs : ∀ i j, |m i| + |m j| = 0 →
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
        Matrix.diagonal (fun i => (m i : ℂ))) i j = 0 := by
    intro i j hij
    have hi : m i = 0 := abs_eq_zero.mp
      ((add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).mp hij).1
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hi]
  rw [rootCost_diagonal _ (fun i => abs_nonneg (m i)) _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralWeight, Matrix.mul_diagonal, Matrix.diagonal_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  ring

theorem norm_trace_cube_le_hessian (M D : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (hD : D.IsHermitian) :
    ‖Matrix.trace ((D * M)^3)‖ ≤
      (10 / 3 : ℝ) * ‖D‖ * hessianCost (M * M) (M * D * M) := by
  let U := star hM.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D' := f D
  let m := hM.eigenvalues
  have hM' : f M = Matrix.diagonal (fun i => (m i : ℂ)) :=
    hM.conjStarAlgAut_star_eigenvectorUnitary
  have hd : D'.IsHermitian := hermitian_unitary_conj U hD
  have hn : ‖D'‖ = ‖D‖ := norm_unitary_conj U D
  have ht : Matrix.trace ((D' * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      Matrix.trace ((D * M)^3) := by
    rw [← hM', ← map_mul, ← map_pow]
    exact trace_unitary_conj U _
  have hp : (M * M).PosSemidef := by
    simpa only [hM.eq] using Matrix.posSemidef_conjTranspose_mul_self M
  have hc := hessianCost_unitary_conj U hp (M * D * M)
  change hessianCost (f (M * M)) (f (M * D * M)) = _ at hc
  simp only [map_mul, hM'] at hc
  rw [hessianCost_diagonal_square] at hc
  have hb := norm_trace_cube_mul_diagonal_le D' hd m
  rw [ht, hn] at hb
  rw [← hc]
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem blocks_mul (A B : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks (A * B) = blocks A * blocks B := by
  exact (Matrix.compRingEquiv Three ι ℂ).map_mul A B

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_star (A : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks Aᴴ = (blocks A)ᴴ := rfl

omit [DecidableEq ι] in
theorem blocks_trace (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix.trace (blocks A) = ∑ v, Matrix.trace (A v v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]

omit [Fintype ι] [DecidableEq ι] in
theorem triangle_hermitian (W : Three → Matrix ι ι ℂ) :
    (triangle W).IsHermitian := by
  change (blocks (triangleBlocks W))ᴴ = blocks (triangleBlocks W)
  rw [← blocks_star]
  congr 1
  ext v w i j
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks, Matrix.conjTranspose_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem blockD_hermitian (D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) : (blockD D).IsHermitian := by
  unfold blockD
  change (blocks (Matrix.diagonal D))ᴴ = blocks (Matrix.diagonal D)
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  have hs : star D = D := funext hD
  rw [hs]

theorem triangle_trace_cube (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    Matrix.trace ((blockD D * triangle W)^3) =
      (6 : ℂ) * (Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  have hreverse :
      Matrix.trace (D 0 * (W 2)ᴴ * D 2 * (W 1)ᴴ * D 1 * (W 0)ᴴ) = star τ := by
    simp only [τ, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (hD _).eq,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hrot (A B C E F G : Matrix ι ι ℂ) :
      Matrix.trace (A * B * C * E * F * G) =
        Matrix.trace (F * G * A * B * C * E) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A * B) (C * E) (F * G)
  have hf1 := hrot (D 1) (W 1) (D 2) (W 2) (D 0) (W 0)
  have hf2 := (hrot (D 2) (W 2) (D 0) (W 0) (D 1) (W 1)).trans hf1
  have hr2 := hrot (D 2) (W 1)ᴴ (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ
  have hr1 := (hrot (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ (D 2) (W 1)ᴴ).trans hr2
  simp only [Matrix.mul_assoc] at hf1 hf2 hr1 hr2 hreverse
  unfold blockD triangle
  rw [← blocks_mul, pow_three, ← blocks_mul, ← blocks_mul, blocks_trace]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, triangleBlocks,
    zero_mul, mul_zero, add_zero, zero_add, ite_true, ite_false, Fin.reduceEq,
    mul_add, add_mul, Matrix.trace_add, Matrix.mul_assoc]
  simp only [Matrix.trace_zero, add_zero, zero_add]
  rw [hf1, hf2, hr1, hr2, hreverse]
  simp only [← Matrix.mul_assoc]
  change τ + star τ + (star τ + τ) + (τ + star τ) = (6 : ℂ) * (τ.re : ℂ)
  apply Complex.ext <;> simp [RCLike.star_def, Complex.mul_re, Complex.mul_im]
  ring

omit [Fintype ι] in
theorem vertexProj_hermitian (v : Three) : (vertexProj (ι := ι) v).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change star (if i.1 = v then (1 : ℂ) else 0) = _
  split_ifs <;> simp

theorem vertexProj_sq (v : Three) : vertexProj (ι := ι) v * vertexProj v = vertexProj v := by
  simp only [vertexProj, Matrix.diagonal_mul_diagonal]
  congr 1
  ext a
  split_ifs <;> simp

omit [Fintype ι] in
theorem sum_vertexProj : ∑ v, vertexProj (ι := ι) v = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [vertexProj, Matrix.sum_apply]
  · simp [vertexProj, Matrix.sum_apply, hab]

theorem vertexProj_commute_blockD (v : Three) (D : Three → Matrix ι ι ℂ) :
    vertexProj v * blockD D = blockD D * vertexProj v := by
  ext a b
  simp only [vertexProj, Matrix.diagonal_mul, Matrix.mul_diagonal, blockD,
    Matrix.comp_apply, Matrix.diagonal_apply]
  by_cases hab : a.1 = b.1
  · simp [hab]
  · simp [hab]

theorem starGram_eq (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = triangle W * vertexProj v * triangle W := by
  simp only [starGram, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (triangle W), vertexProj_sq]

theorem starInsert_eq (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = triangle W * vertexProj v * blockD D * triangle W := by
  simp only [starInsert, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  have hp := vertexProj_commute_blockD v D
  calc
    _ = triangle W * (vertexProj v * (blockD D * vertexProj v)) * triangle W := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hp, ← Matrix.mul_assoc (vertexProj v), vertexProj_sq];
                simp only [Matrix.mul_assoc]

theorem sum_starGram (W : Three → Matrix ι ι ℂ) :
    ∑ v, starGram W v = triangle W * triangle W := by
  simp_rw [starGram_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem sum_starInsert (W D : Three → Matrix ι ι ℂ) :
    ∑ v, starInsert W D v = triangle W * blockD D * triangle W := by
  simp_rw [starInsert_eq]
  rw [← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem starGram_le (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v ≤ triangle W * triangle W := by
  rw [← sum_starGram]
  exact Finset.single_le_sum (fun w _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar W w)).nonneg) (Finset.mem_univ v)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_common_three (P K : Fin 3 → Matrix ι ι ℂ)
    {Q : Matrix ι ι ℂ} (hPQ : ∀ v, P v ≤ Q)
    (hsol : ∀ v, ∃ X, sylv (CFC.sqrt (P v)) X = K v) :
    hessianCost Q (∑ v, K v) ≤ 3 * ∑ v, hessianCost (P v) (K v) := by
  have hq : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hsolQ (v : Fin 3) : ∃ X, sylv (CFC.sqrt Q) X = K v :=
    sylv_solvable_mono (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v)))
      hq.isHermitian (hsol v) (CFC.monotone_sqrt (hPQ v))
  calc
    _ ≤ 3 * ∑ v, hessianCost Q (K v) := by
      simpa only [Fin.sum_univ_three, hessianCost] using
        rootCost_three_le hq (hsolQ 0) (hsolQ 1) (hsolQ 2)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
      (fun v _ => hessianCost_antitone (hsol v) (hPQ v))) (by norm_num)

theorem triangle_common_metric (W D : Three → Matrix ι ι ℂ) :
    hessianCost (triangle W * triangle W) (triangle W * blockD D * triangle W) ≤
      3 * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  rw [← sum_starInsert]
  exact hessianCost_common_three (starGram W) (starInsert W D)
    (starGram_le W) (fun v => sylv_solvable_inserted_gram (rowStar W v) (blockD D))

theorem triangle_real_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    |(Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re| ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  have h := norm_trace_cube_le_hessian (triangle W) (blockD D)
    (triangle_hermitian W) (blockD_hermitian D hD)
  rw [triangle_trace_cube W D hD, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hm := triangle_common_metric W D
  have hc := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (10 / 3 : ℝ) * ‖blockD D‖ by positivity)
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem insertedCost_right_unitary (R L : Matrix ι ι ℂ)
    (U : unitary (Matrix ι ι ℂ)) :
    hessianCost ((R * (U : Matrix ι ι ℂ))ᴴ * (R * (U : Matrix ι ι ℂ)))
      ((R * (U : Matrix ι ι ℂ))ᴴ * L * (R * (U : Matrix ι ι ℂ))) =
      hessianCost (Rᴴ * R) (Rᴴ * L * R) := by
  simpa only [conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      hessianCost_unitary_conj (star U) (Matrix.posSemidef_conjTranspose_mul_self R)
        (Rᴴ * L * R)

omit [Fintype ι] [DecidableEq ι] in
theorem rowPhase_norm (z : ℂ) (hz : ‖z‖ = 1) (v : Three) (a : BlockSpace ι) :
    ‖rowPhase z v a‖ = 1 := by
  unfold rowPhase
  split_ifs <;> simp [hz]

theorem rowStar_phase (z : ℂ) (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (phaseEdge z W) v = rowStar W v * Matrix.diagonal (rowPhase z v) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases v <;> fin_cases a <;> fin_cases b
  all_goals simp [rowStar, vertexProj, triangle, Matrix.comp_apply,
    triangleBlocks, phaseEdge, rowPhase, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, smul_eq_mul, mul_comm]

theorem starCost_phase (z : ℂ) (hz : ‖z‖ = 1)
    (W D : Three → Matrix ι ι ℂ) (v : Three) :
    hessianCost (starGram (phaseEdge z W) v) (starInsert (phaseEdge z W) D v) =
      hessianCost (starGram W v) (starInsert W D v) := by
  let U := diagonalUnitary (rowPhase (ι := ι) z v) (rowPhase_norm z hz v)
  have he : rowStar (phaseEdge z W) v = rowStar W v * (U : Matrix _ _ ℂ) :=
    rowStar_phase z W v
  simp only [starGram, starInsert, he]
  exact insertedCost_right_unitary (rowStar W v) (blockD D) U

omit [Fintype ι] [DecidableEq ι] in
theorem exists_phase_norm (τ : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ z * τ = (‖τ‖ : ℂ) := by
  by_cases hτ : τ = 0
  · exact ⟨1, norm_one, by simp [hτ]⟩
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.mpr hτ
  have hnc : (‖τ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨star τ / (‖τ‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      (star τ / (‖τ‖ : ℂ)) * τ = (τ * star τ) / (‖τ‖ : ℂ) := by ring
      _ = (‖τ‖ : ℂ)^2 / (‖τ‖ : ℂ) := by rw [RCLike.star_def, Complex.mul_conj']
      _ = _ := by field_simp

theorem mixed_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    ‖Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)‖ ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  obtain ⟨z, hz, he⟩ := exists_phase_norm τ
  have ht : Matrix.trace (D 0 * phaseEdge z W 0 * D 1 *
      phaseEdge z W 1 * D 2 * phaseEdge z W 2) = z * τ := by
    simp [phaseEdge, τ]
  have h := triangle_real_trace_le (phaseEdge z W) D hD
  rw [ht, he] at h
  simp only [Complex.ofReal_re, abs_of_nonneg (norm_nonneg τ)] at h
  simpa only [starCost_phase z hz] using h

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_diag (W : Three → Matrix ι ι ℂ) (v : Three) :
    triangleBlocks W v v = 0 := by
  fin_cases v <;> simp [triangleBlocks]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weightedGram_posSemidef (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : (weightedGram B w).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hw i))).conjTranspose_mul_mul_same B

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

lemma weightedGram_smul (B : Matrix ι ι ℂ) (c : ℝ) (w : ι → ℝ) :
    weightedGram B (fun i => c * w i) = c • weightedGram B w := by
  have he : Matrix.diagonal (fun i => ((c * w i : ℝ) : ℂ)) =
      c • Matrix.diagonal (fun i => (w i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  unfold weightedGram
  rw [he, Matrix.mul_smul, Matrix.smul_mul]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma vertexRoot_star (g : Three → ι → ℝ) : (vertexRoot g)ᴴ = vertexRoot g := by
  unfold vertexRoot
  rw [Matrix.diagonal_conjTranspose]
  simp

lemma vertexRoot_sq (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * vertexRoot g = Matrix.diagonal (fun a => (g a.1 a.2 : ℂ)) := by
  rw [vertexRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a.1 a.2)]

lemma vertexRoot_commute_vertexProj (g : Three → ι → ℝ) (v : Three) :
    vertexRoot g * vertexProj v = vertexProj v * vertexRoot g := by
  dsimp only [vertexRoot, vertexProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

lemma triangle_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    triangle (weightedArray A g) = vertexRoot g * triangle A * vertexRoot g := by
  ext ⟨v,i⟩ ⟨w,j⟩
  fin_cases v <;> fin_cases w <;>
    simp [triangle, triangleBlocks, blocks, weightedArray, vertexRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      mul_comm, mul_left_comm, mul_assoc] <;> first | exact Or.inl (mul_comm _ _) | ring

lemma rowStar_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :
    rowStar (weightedArray A g) v = vertexRoot g * rowStar A v * vertexRoot g := by
  unfold rowStar
  rw [triangle_weightedArray]
  simp only [← Matrix.mul_assoc]
  rw [← vertexRoot_commute_vertexProj]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

lemma starGram_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    starGram (weightedArray A g) v = weightedGram (rowBare A g v) (fun a => g a.1 a.2) := by
  have hr : rowStar (weightedArray A g) v = vertexRoot g * rowBare A g v := by
    rw [rowStar_weightedArray, rowBare, Matrix.mul_assoc]
  rw [starGram, hr, Matrix.conjTranspose_mul, vertexRoot_star]
  unfold weightedGram
  calc
    _ = (rowBare A g v)ᴴ * (vertexRoot g * vertexRoot g) * rowBare A g v := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [vertexRoot_sq g hg]

lemma rowBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ w, w ≠ v → ∀ i, g' w i = g w i) : rowBare A g' v = rowBare A g v := by
  ext a b
  dsimp only [rowBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, rowStar_apply]
  by_cases ha : a.1 = v
  · rw [ite_eq_left ha]
    by_cases hb : b.1 = v
    · rw [ha, hb, triangleBlocks_diag, Matrix.zero_apply, zero_mul, zero_mul]
    · rw [he b.1 hb]
  · rw [ite_eq_right ha, zero_mul, zero_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedCompare ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weightedGram_sub (B : Matrix ι ι ℂ) (f g : ι → ℝ) :
    weightedGram B (fun i => f i-g i) = weightedGram B f-weightedGram B g := by
  unfold weightedGram
  have hd : Matrix.diagonal (fun i => ((f i-g i:ℝ):ℂ)) =
      Matrix.diagonal (fun i => (f i:ℂ))-Matrix.diagonal (fun i => (g i:ℂ)) := by
    rw [Matrix.diagonal_sub]
    simp only [Complex.ofReal_sub]
  rw [hd,Matrix.mul_sub,Matrix.sub_mul]

lemma weightedGram_mono (B : Matrix ι ι ℂ) (f g : ι → ℝ) (hfg : ∀ i, f i ≤ g i) :
    weightedGram B f ≤ weightedGram B g := by
  rw [← sub_nonneg,← weightedGram_sub]
  exact (weightedGram_posSemidef B (fun i => sub_nonneg.mpr (hfg i))).nonneg

lemma hessianCost_smul_direction {P K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (c : ℝ) :
    hessianCost P (c • K) = c^2*hessianCost P K := by
  exact rootCost_smul_direction (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol c

omit [Fintype ι] in
lemma blockD_real_diagonal (d : Three → ι → ℝ) :
    blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ))) =
      Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2:ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v=w <;> by_cases hi : i=j <;>
    simp [blockD,blocks,Matrix.diagonal,hv,hi,Prod.mk.injEq]

lemma norm_blockD_real_diagonal_le (d : Three → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ v i, |d v i| ≤ C) :
    ‖blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ)))‖ ≤ C := by
  rw [blockD_real_diagonal,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun a => by simpa using hd a.1 a.2)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StarInsertion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (rowBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      starInsert (weightedArray A g) (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) v := by
  unfold starInsert
  rw [rowStar_weightedArray]
  unfold weightedGram rowBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma localGram_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localGram A h u p σ v v = starGram (heatArray A h u p σ) v := by
  simp only [localGram, fixedBase, ite_true]
  exact (starGram_weightedArray A _ (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1) else 0) := by
  funext a
  simp only [groupFirst, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localFirst_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localFirst A h u p σ v v =
      starInsert (heatArray A h u p σ) (heatScores u p σ) v := by
  simp only [localFirst, fixedBase, ite_true, groupFirst_eq_insert]
  rw [rowBare_insert A (heatWeights h u p σ)
    (fun w i => if w = v then score (u i) (p w) (σ w) else 0)
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v]
  rw [starInsert_eq_insertRow, starInsert_eq_insertRow]
  simp only [heatArray, heatScores, ite_true]

lemma heatCost_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    heatCost A h u p σ v v = hessianCost (starGram (heatArray A h u p σ) v)
      (starInsert (heatArray A h u p σ) (heatScores u p σ) v) := by
  rw [heatCost, localGram_center A hh u p hσ, localFirst_center A hh u p hσ]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.NormBounds ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianCost_nonneg (P K : Matrix ι ι ℂ) : 0 ≤ hessianCost P K := by
  unfold hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt P) K))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneDissipation ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma strictRate_pos (i w : Three) : 0 < strictRate i w := by
  unfold strictRate; split_ifs <;> norm_num

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedTraceOrder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowBare_strict_eq_base (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p : Three → ℝ) (s : ℝ) (v : Three) :
    rowBare A (heatWeights h u p (fun z => strictRate v z*s)) v =
      rowBare A (heatWeights h u p (fun _ => (11/10)*s)) v := by
  apply rowBare_congr
  intro w hw i
  simp [heatWeights,strictRate,hw]

omit [Fintype ι] [DecidableEq ι] in
lemma heatWeights_strict_le_base {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) (v w : Three) (i : ι) :
    heatWeights h u p (fun z => strictRate v z*s) w i ≤
      Real.sqrt (11/10)*heatWeights h u p (fun _ => (11/10)*s) w i := by
  have hr : 1 ≤ Real.sqrt (11/10) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  by_cases hw : w=v
  · subst w
    simp only [heatWeights,strictRate,ite_true,one_mul,weight]
    have hd := mul_le_mul_of_nonneg_left (density_le_lambda hs (u i-p v)) hh.le
    simpa only [mul_left_comm] using hd
  · simp only [heatWeights,strictRate,ite_eq_right hw]
    exact le_mul_of_one_le_left (weight_pos hh (by positivity) _ _).le hr

lemma strict_starGram_le_base (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starGram (heatArray A h u p (fun z => strictRate v z*s)) v ≤
      Real.sqrt (11/10) • starGram (heatArray A h u p (fun _ => (11/10)*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray
  rw [starGram_weightedArray _ _ ht,starGram_weightedArray _ _ hb,
    rowBare_strict_eq_base,← weightedGram_smul]
  exact weightedGram_mono _ _ _ (fun a => heatWeights_strict_le_base hh hs u p v a.1 a.2)

lemma windowInsertion_eq_score (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v =
      Real.sqrt s • starInsert (heatArray A h u p (fun z => strictRate v z*s))
        (heatScores u p (fun z => strictRate v z*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray windowDiags heatScores
  rw [← rowBare_insert _ _ _ hb,← rowBare_insert _ _ _ ht,
    rowBare_strict_eq_base,← weightedGram_smul]
  apply weightedGram_rowBare_congr
  intro i
  dsimp only
  simp only [heatWeights,strictRate,ite_true,one_mul,weight]
  have hn : density ((11/10)*s) (u i-p v) ≠ 0 := (density_pos (by positivity) _).ne'
  unfold windowRatio
  rw [oddWindow_score hs]
  simp only [div_eq_mul_inv]
  calc
    _ = (Real.sqrt s*(h*density s (u i-p v)*score (u i) (p v) s))*
        (density ((11/10)*s) (u i-p v)*(density ((11/10)*s) (u i-p v))⁻¹) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hn]; ring

lemma windowStarCost_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    hessianCost (starGram (heatArray A h u p (fun _ => (11/10)*s)) v)
      (starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v) ≤
      2*s*heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hσ : ∀ z, 0 < strictRate v z*s := fun z => mul_pos (strictRate_pos v z) hs
  let P := starGram (heatArray A h u p (fun z => strictRate v z*s)) v
  let K := starInsert (heatArray A h u p (fun z => strictRate v z*s))
    (heatScores u p (fun z => strictRate v z*s)) v
  have hsol : ∃ Y, sylv (CFC.sqrt P) Y = K := sylv_solvable_inserted_gram _ _
  have hsol' : ∃ Y, sylv (CFC.sqrt P) Y = Real.sqrt s • K := by
    obtain ⟨Y,hY⟩ := hsol
    exact ⟨Real.sqrt s • Y,by rw [sylv_smul_right,hY]⟩
  have hc := hessianCost_le_of_le_smul
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar (heatArray A h u p (fun _ => (11/10)*s)) v))
    hsol' (by positivity : 0 < Real.sqrt (11/10)) (strict_starGram_le_base A hh hs u p v)
  rw [windowInsertion_eq_score A hh hs,heatCost_center A hh u p hσ]
  change hessianCost _ (Real.sqrt s • K) ≤ 2*s*hessianCost P K
  rw [hessianCost_smul_direction hsol,Real.sq_sqrt hs.le] at hc
  have hr : Real.sqrt (Real.sqrt (11/10)) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · rw [Real.sqrt_le_iff]; norm_num
  have hn : 0 ≤ hessianCost P K := hessianCost_nonneg _ _
  exact hc.trans (by
    calc
      _ ≤ 2*(s*hessianCost P K) := mul_le_mul_of_nonneg_right hr (mul_nonneg hs.le hn)
      _ = _ := by ring)

lemma windowTrace_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) :
    ‖windowTrace A h u p s‖ ≤ (440/3)*s*∑ v,
      heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hD (v : Three) : (windowDiags u p s v).IsHermitian := by
    unfold windowDiags Matrix.IsHermitian
    rw [Matrix.diagonal_conjTranspose]
    simp
  have hd : ‖blockD (windowDiags u p s)‖ ≤ 44 :=
    norm_blockD_real_diagonal_le _ (by norm_num) (fun v i => abs_windowRatio_le hs _)
  have hm := mixed_trace_le (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) hD
  have hi := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) =>
    windowStarCost_le A hh hs u p v)
  apply hm.trans
  calc
    _ ≤ (5/3:ℝ)*44*(∑ v, 2*s*heatCost A h u p (fun z => strictRate v z*s) v v) := by
      gcongr
      exact Finset.sum_nonneg (fun v _ => hessianCost_nonneg _ _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.windowTrace_le.{uι} := @_root_.OAI.TriangularHilbert.Heat.windowTrace_le.{uι}
