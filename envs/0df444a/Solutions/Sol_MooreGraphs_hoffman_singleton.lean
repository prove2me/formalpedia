-- Prove2me | solution 1 for MooreGraphs.hoffman_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:50.474971+00:00
-- url     : https://prove2.me/submissions/8f18c297-6662-4093-99ed-1305c9830cac

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Definitions.Def_MooreLib_MooreGraphs
public import Theorems.Thm_MooreGraphs_isSRGWith
public import Theorems.Thm_MooreGraphs_eigen_cubic
public import Theorems.Thm_MooreGraphs_final_arith
public import Theorems.Thm_MooreGraphs_trace_sq_eq_sum


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  classical
  have hsrg := isSRGWith G hreg hdiam hgirth
  have hA : (adjMatrix ℝ G).IsHermitian := isHermitian_adjMatrix (R := ℝ) G
  set ev := hA.eigenvalues
  have hcard : (Fintype.card V : ℝ) = k ^ 2 + 1 := by exact_mod_cast hsrg.card
  have hcub : ∀ i, (ev i ^ 2 + ev i - (k - 1)) * (ev i - k) = 0 := fun i =>
    eigen_cubic G hsrg (x := (hA.eigenvectorBasis i).ofLp)
      ((WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i)
      (hA.mulVec_eigenvectorBasis i)
  have htr1 : ∑ i, ev i = 0 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [trace_adjMatrix] at this
    simpa using this.symm
  have htr2 : ∑ i, ev i ^ 2 = (k ^ 2 + 1) * k := by
    rw [← trace_sq_eq_sum hA, pow_two, Matrix.trace]
    simp only [Matrix.diag_apply, adjMatrix_mul_self_apply_self, hreg.degree_eq]
    simp [hcard]
  set g : V → ℝ := fun i => if ev i = k then 1 else 0
  have hf : ∀ i, ev i ^ 2 + ev i - (k - 1) = (k ^ 2 + 1) * g i := by
    intro i
    by_cases h : ev i = k
    · simp only [g, h, ite_true]; ring
    · simp only [g, h, ite_false, mul_zero]
      exact (mul_eq_zero.1 (hcub i)).resolve_right (sub_ne_zero.2 h)
  have hg : ∑ i, g i = 1 := by
    have h1 : ∑ i, (ev i ^ 2 + ev i - (k - 1)) = (k ^ 2 + 1) * ∑ i, g i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hf i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, htr1, htr2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcard] at h1
    have hpos : (k : ℝ) ^ 2 + 1 ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos (h1.symm.trans (by ring : _ = ((k : ℝ) ^ 2 + 1) * 1))
  set s := √(4 * (k : ℝ) - 3)
  have hs : s ^ 2 = 4 * k - 3 := Real.sq_sqrt (by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  set ε : V → ℤ := fun i => if ev i = k then 0 else if 2 * ev i + 1 = s then 1 else -1
  have hε : ∀ i, 2 * ev i + 1 = ε i * s + (2 * k + 1) * g i := by
    intro i
    by_cases h : ev i = k
    · simp [ε, g, h]
    · have hq : ev i ^ 2 + ev i - (k - 1) = 0 :=
        (mul_eq_zero.1 (hcub i)).resolve_right (sub_ne_zero.2 h)
      have hsq : (2 * ev i + 1) ^ 2 = s ^ 2 := by rw [hs]; linear_combination 4 * hq
      by_cases h' : 2 * ev i + 1 = s
      · simp [ε, g, h, h']
      · have : 2 * ev i + 1 = -s := ((sq_eq_sq_iff_eq_or_eq_neg).1 hsq).resolve_left h'
        simp [ε, g, h, this]
  have hsum : ∑ i, (2 * ev i + 1) = ((∑ i, ε i : ℤ) : ℝ) * s + (2 * k + 1) := by
    rw [Finset.sum_congr rfl fun i _ => hε i, Finset.sum_add_distrib, ← Finset.mul_sum, hg,
      ← Finset.sum_mul]
    push_cast; ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, htr1, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard] at hsum
  exact final_arith hk (∑ i, ε i) (by linear_combination -hsum)
end MooreGraphs
