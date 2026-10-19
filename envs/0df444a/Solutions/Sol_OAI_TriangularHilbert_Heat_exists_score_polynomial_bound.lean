-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.exists_score_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:34:52.0053+00:00
-- url     : https://prove2.me/submissions/a00dbe04-1b61-410d-b638-96d08adb5c06

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneDom.lean:L138-L175
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.exists_score_polynomial_bound. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.GaussianDom ----
namespace OAI

section

namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma score_le_linear {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) (u p : ℝ) :
    |score u p σ| ≤ (|u|+|p|)/a := by
  unfold score
  rw [abs_div, abs_of_pos (ha.trans_le haσ)]
  exact (div_le_div_of_nonneg_right (by simpa using abs_sub_le u 0 p) (ha.trans_le haσ).le).trans
    (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) ha haσ)

lemma one_le_planePoly (z : ℝ × ℝ) : 1 ≤ planePoly z := by
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]
lemma planePoly_nonneg (z : ℝ × ℝ) : 0 ≤ planePoly z := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_planePoly z)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneDom ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1+x^2 := by
  nlinarith [sq_nonneg (|x|-1), sq_abs x]

lemma planePoly_ge_first (z : ℝ × ℝ) : |z.1| ≤ planePoly z := by
  have := abs_le_one_add_sq z.1
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma planePoly_ge_second (z : ℝ × ℝ) : |z.2| ≤ planePoly z := by
  have := abs_le_one_add_sq z.2
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]

lemma chart_abs_bound {D d : ℝ} (hd : |d| ≤ D) (i w : Three) (z : ℝ × ℝ) :
    |chart i d z w| ≤ (D+2) * planePoly z := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hP := one_le_planePoly z
  have hx := planePoly_ge_first z
  have hy := planePoly_ge_second z
  have hDP : D ≤ D * planePoly z := by nlinarith
  have hab : |d-z.1-z.2| ≤ |d|+|z.1|+|z.2| := by
    calc
      _ ≤ |d-z.1| + |z.2| := by simpa using abs_sub_le (d-z.1) 0 z.2
      _ ≤ _ := by simpa using add_le_add_right (abs_sub_le d 0 z.1) (abs z.2)
  fin_cases i <;> fin_cases w <;> simp [chart] <;> nlinarith

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma exists_score_polynomial_bound (u : ι → ℝ) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D →
      ∀ (σ : Three → ℝ), (∀ w, a ≤ σ w) → ∀ w j,
        |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z ∧
        |score (u j) (chart i d z w) (σ w)^2 - (σ w)⁻¹| ≤ (C^2+a⁻¹) * planePoly z^2 := by
  let U := ∑ j, |u j|
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg (u j))
  have hu j : |u j| ≤ U := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ j)
  let C := (U+D+2)/a
  have hC : 0 ≤ C := div_nonneg (by linarith) ha.le
  refine ⟨C,hC,?_⟩
  intro i d z hd σ hσ w j
  have hP := one_le_planePoly z
  have hpn := planePoly_nonneg z
  have hsp : 0 < σ w := ha.trans_le (hσ w)
  have hs : |score (u j) (chart i d z w) (σ w)| ≤ C * planePoly z := by
    calc
      _ ≤ (|u j|+|chart i d z w|)/a := score_le_linear ha (hσ w) _ _
      _ ≤ (U+(D+2)*planePoly z)/a := by gcongr; exacts [hu j, chart_abs_bound hd i w z]
      _ ≤ C * planePoly z := by
        dsimp [C]
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
        nlinarith
  have hinv : (σ w)⁻¹ ≤ a⁻¹ := by
    simp only [← one_div]
    exact one_div_le_one_div_of_le ha (hσ w)
  have hs2 : score (u j) (chart i d z w) (σ w)^2 ≤ C^2 * planePoly z^2 := by
    have := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hpn)).2 hs
    simpa only [sq_abs, mul_pow] using this
  refine ⟨hs,?_⟩
  calc
    _ ≤ score (u j) (chart i d z w) (σ w)^2 + (σ w)⁻¹ := by
      calc
        _ ≤ |score (u j) (chart i d z w) (σ w)^2| + |(σ w)⁻¹| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (inv_pos.mpr hsp)]
    _ ≤ C^2 * planePoly z^2 + a⁻¹ := add_le_add hs2 hinv
    _ ≤ _ := by nlinarith [inv_pos.mpr ha, sq_nonneg (planePoly z-1)]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.exists_score_polynomial_bound.{uι} := @_root_.OAI.TriangularHilbert.Heat.exists_score_polynomial_bound.{uι}
