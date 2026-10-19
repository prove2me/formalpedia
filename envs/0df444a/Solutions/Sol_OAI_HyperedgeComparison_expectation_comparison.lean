-- Prove2me | solution 1 for OAI.HyperedgeComparison.expectation_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:12:49.036152+00:00
-- url     : https://prove2.me/submissions/0393be09-e5ec-41b8-8c36-0453ce58eadb

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1397-L1438
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.expectation_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_baseMatrix_diag_pos
import Theorems.Thm_OAI_HyperedgeComparison_coeff_nonneg
import Theorems.Thm_OAI_HyperedgeComparison_exists_unique_firstRoot
import Theorems.Thm_OAI_HyperedgeComparison_inverse_last_diag_mul
import Theorems.Thm_OAI_HyperedgeComparison_inverse_offdiag_nonpos

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem cluster_eq_of_connected {H : Hypergraph V E} {ω : E → Bool} {D : Set V}
    {s t : V} (hst : Connected H ω D s t) :
    cluster H ω D s = cluster H ω D t := by
  ext y
  exact ⟨fun hy => connected_trans (connected_symm hst) hy,
    fun hy => connected_trans hst hy⟩

/-- The first-listed-node partition, as a pointwise identity for any cluster
functional. This is stronger than its integrated mass identity H d = 1. -/
theorem sum_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) (F : Set V → ℝ) :
    (∑ k, if firstRoot H x ω D k i then F (cluster H ω D (x k)) else 0) =
      F (cluster H ω D (x i)) := by
  classical
  obtain ⟨k, hk, huniq⟩ := exists_unique_firstRoot H x ω D i
  rw [Finset.sum_eq_single k]
  · rw [ite_eq_left hk, cluster_eq_of_connected hk.2]
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (huniq j h))]
  · simp

section FiniteLaw
variable [Fintype E]

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

/-- The first-listed cluster columns partition every row. -/
theorem baseMatrix_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) :
    baseMatrix H p x *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  unfold Matrix.mulVec dotProduct baseMatrix column
  simp only [mul_one]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hs (ω : E → Bool) := sum_firstRoot H x ω ∅ i (fun _ => (1:ℝ))
  simp_rw [hs]
  simp

/-- Consequently each row of the inverse also sums to one. -/
theorem inverse_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  calc
    _ = (baseMatrix H p x)⁻¹ *ᵥ (baseMatrix H p x *ᵥ (fun _ => 1)) :=
      congrArg (fun v => (baseMatrix H p x)⁻¹ *ᵥ v) (baseMatrix_mulVec_one H p x).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem expectationVector_eq_sum_columns {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) :
    expectationVector H p x F = ∑ k, column H p x k F := by
  funext i
  simp only [Finset.sum_apply, column]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [sum_firstRoot]
  rfl

/-- Increasing observables give nonnegative inverse expectation vectors. -/
theorem inverse_expectation_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (i : Fin n) :
    0 ≤ ((baseMatrix H p x)⁻¹ *ᵥ expectationVector H p x F) i := by
  rw [expectationVector_eq_sum_columns, Matrix.mulVec_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => coeff_nonneg H p hp x hx k F
    (fun U _ => hF0 U) (hFm.monotoneOn _) i)

/-- Scalar consequence of the cone: a target observable large at every earlier
listed vertex must have a correspondingly large expectation at the last one. -/
theorem expectation_comparison [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ expectationVector H p x F j) :
    b * (1 - baseMatrix H p x (Fin.last n) (Fin.last n)) ≤
      expectationVector H p x F (Fin.last n) := by
  classical
  let l := Fin.last n
  let M := baseMatrix H p x
  let y := expectationVector H p x F
  have hrow : (∑ j, M⁻¹ l j) = 1 := by
    have h := congrFun (inverse_mulVec_one H p hp x hx) l
    simpa [Matrix.mulVec, dotProduct, M] using h
  have hpos : 0 ≤ ∑ j, M⁻¹ l j * y j :=
    inverse_expectation_nonneg H p hp x hx F hF0 hFm l
  have hdiff : (∑ j, M⁻¹ l j * (y j - b)) ≤ M⁻¹ l l * (y l - b) := by
    calc
      _ ≤ ∑ j, if j = l then M⁻¹ l l * (y l - b) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = l
        · subst j; simp
        · rw [ite_eq_right hj]
          exact mul_nonpos_of_nonpos_of_nonneg
            (inverse_offdiag_nonpos H p hp x hx (Ne.symm hj)) (sub_nonneg.mpr (hb j hj))
      _ = _ := by simp
  simp_rw [mul_sub] at hdiff
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul] at hdiff
  have hlow : -b ≤ M⁻¹ l l * (y l - b) := by linarith
  have hd : 0 < M l l := baseMatrix_diag_pos H p hp x hx l
  have hprod : M⁻¹ l l * M l l = 1 := inverse_last_diag_mul H p hp x hx
  have hh := mul_le_mul_of_nonneg_right hlow hd.le
  have heq : M⁻¹ l l * (y l - b) * M l l = y l - b := by
    calc
      _ = (M⁻¹ l l * M l l) * (y l - b) := by ring
      _ = y l - b := by rw [hprod, one_mul]
  rw [heq] at hh
  change b * (1 - M l l) ≤ y l
  linarith

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.expectation_comparison.{uE,uV} := @_root_.OAI.HyperedgeComparison.expectation_comparison.{uE,uV}
