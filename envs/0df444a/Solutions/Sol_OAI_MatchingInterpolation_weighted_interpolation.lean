-- Prove2me | solution 1 for OAI.MatchingInterpolation.weighted_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:04:41.488876+00:00
-- url     : https://prove2.me/submissions/7e69a426-d91e-4ca9-9c5d-27418d706c99

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean:L188-L208
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingInterpolation.weighted_interpolation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Theorems.Thm_OAI_MatchingSmoothing_mul_mem_lowDegree

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma lowDegree_mono (x : E → X → ℝ) {d e : ℕ} (h : d ≤ e) :
    lowDegree x d ≤ lowDegree x e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hf⟩
  exact ⟨l, hl.trans h, hf⟩

lemma one_mem_lowDegree (x : E → X → ℝ) (d : ℕ) : (1 : X → ℝ) ∈ lowDegree x d :=
  Submodule.subset_span ⟨[], Nat.zero_le _, rfl⟩

lemma coord_mem_lowDegree (x : E → X → ℝ) (e : E) : x e ∈ lowDegree x 1 := by
  apply Submodule.subset_span
  exact ⟨[e], by simp, by simp⟩

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialInterpolation ----
namespace OAI

namespace MatchingInterpolation
open Polynomial
open MatchingSmoothing

lemma power_interpolation (d k : ℕ) (hk : k ≤ d) (x : ℝ) :
    x^k = ∑ j : Fin (d+1), (j:ℝ)^k * (lagrange d j).eval x := by
  have hinj : Set.InjOn (fun j : Fin (d+1) => (j:ℝ)) (Finset.univ : Finset (Fin (d+1))) := by
    intro i _ j _ h
    apply Fin.ext
    change (i.val:ℝ) = (j.val:ℝ) at h
    exact Nat.cast_inj.mp h
  have hdeg : (Polynomial.X^k : ℝ[X]).degree < (Finset.univ : Finset (Fin (d+1))).card := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hk
  have he := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate hinj hdeg)
  simpa [Lagrange.interpolate_apply, lagrange, Polynomial.eval_finsetSum] using he

lemma list_product_counts (l : List (Fin 3)) (x : Point) :
    (l.map x).prod = ∏ a, x a ^ l.count a := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  have hn : a ∉ l := fun hx => ha (List.mem_toFinset.mpr hx)
  simp [List.count_eq_zero_of_not_mem hn]

lemma monomial_interpolation (d : ℕ) (l : List (Fin 3)) (hl : l.length ≤ d) (x : Point) :
    (l.map x).prod = ∑ g : GridIndex d, tensorBasis d g x * (l.map (gridNode g)).prod := by
  rw [list_product_counts]
  have hp (a : Fin 3) := power_interpolation d (l.count a)
    (List.count_le_length.trans hl) (x a)
  simp_rw [hp]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib, list_product_counts, mul_comm]
  rfl

lemma lowDegree_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (x : Point) : P x = ∑ g : GridIndex d, tensorBasis d g x * P (gridNode g) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have he (v : Point) : (l.map coord).prod v = (l.map v).prod := by
      induction l with
      | nil => rfl
      | cons a l ih => simpa [coord] using congrArg (fun t => v a*t) (ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ l.length) hl))
    simp_rw [he]
    exact monomial_interpolation d l hl x
  | zero => simp
  | add f g _ _ hf hg => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hf, hg]
  | smul c f _ hf =>
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm _ c, Finset.mul_sum, hf]

lemma linePolynomial_eval (d : ℕ) (g : GridIndex d) (v : Point) (t : ℝ) :
    (linePolynomial d g v).eval t = tensorBasis d g (fun a => t * v a) := by
  simp only [linePolynomial, tensorBasis, Polynomial.eval_prod, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro a _
  rw [mul_comm]

lemma lowDegree_affine_pullback (d : ℕ) (P : Point → ℝ)
    (hP : P ∈ lowDegree coord d) (b : Point) (L : ℝ) :
    (fun x : Point => P (fun a => b a + L*x a)) ∈ lowDegree coord d := by
  have hcoord (a : Fin 3) : (fun x : Point => b a + L*x a) ∈ lowDegree coord 1 := by
    have hc := (lowDegree coord 1).smul_mem (b a) (one_mem_lowDegree coord 1)
    have hx := (lowDegree coord 1).smul_mem L (coord_mem_lowDegree coord a)
    convert (lowDegree coord 1).add_mem hc hx using 1
    ext x
    simp [coord]
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    apply lowDegree_mono coord hl
    clear hl
    induction l with
    | nil => exact one_mem_lowDegree coord 0
    | cons a l ih =>
      convert mul_mem_lowDegree coord (hcoord a) ih using 1
      · simp only [List.length_cons, Nat.add_comm]
      · rfl
  | zero => exact (lowDegree coord d).zero_mem
  | add f g _ _ hf hg => exact (lowDegree coord d).add_mem hf hg
  | smul c f _ hf => exact (lowDegree coord d).smul_mem c hf

lemma weighted_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (L : ℝ) (hL : L ≠ 0) :
    P (origin + dirA) + P (origin + dirB) - P (origin + dirStar) -
      2 * P (origin + dirP) + P origin =
      ∑ g : GridIndex d, weight d L g * P (fun a => origin a + L*(g a:ℝ)) := by
  let Q : Point → ℝ := fun x => P (fun a => origin a + L*x a)
  have hQ : Q ∈ lowDegree coord d := lowDegree_affine_pullback d P hP origin L
  have he (v : Point) : P (origin + v) =
      ∑ g : GridIndex d, (linePolynomial d g v).eval L⁻¹ *
        P (fun a => origin a + L*(g a:ℝ)) := by
    have hi := lowDegree_interpolation d Q hQ (fun a => L⁻¹*v a)
    have hx : (fun a => origin a + L*(L⁻¹*v a)) = origin + v := by
      funext a
      simp [hL]
    simpa only [Q, hx, ← linePolynomial_eval, gridNode] using hi
  have he0 := he 0
  rw [add_zero] at he0
  rw [he dirA, he dirB, he dirStar, he dirP, he0]
  simp only [weight, weightPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    add_mul, sub_mul, mul_assoc, ← Finset.mul_sum]

end MatchingInterpolation

end OAI

-- ---- platform node ----
open OAI OAI.MatchingInterpolation
open Polynomial
open MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingInterpolation.weighted_interpolation := @_root_.OAI.MatchingInterpolation.weighted_interpolation
