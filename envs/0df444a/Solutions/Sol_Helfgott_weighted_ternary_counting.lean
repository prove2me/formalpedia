-- Prove2me | solution 1 for Helfgott.weighted_ternary_counting
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:04:43.025526+00:00
-- url     : https://prove2.me/submissions/716fe302-b8a5-4932-8ffb-388c7b648c71

import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
The absolutely convergent weighted ternary counting identity. This is the
analytic-to-arithmetic interface in H. A. Helfgott, arXiv:1312.7748v2,
equations (1.3) and (7.49). The series are not truncated: the formulation
retains the tails of the Gaussian-based smoothing functions.

Written by Codex. The proof uses Mathlib's Fourier orthogonality and
dominated convergence for absolutely summable series.
-/

open MeasureTheory
open scoped BigOperators

namespace Helfgott

lemma mem_tripleIndices (t : (ℕ × ℕ) × ℕ) (N : ℕ) :
    t ∈ tripleIndices N ↔ t.1.1 + t.1.2 + t.2 = N := by
  simp only [tripleIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, h⟩

lemma integral_character (k : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourier k α ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

lemma norm_term (d : ℂ) (k : ℤ) (α : AddCircle (1 : ℝ)) :
    ‖d * fourier k α‖ = ‖d‖ := by
  simp [fourier_apply, Circle.norm_coe]

lemma summable_twisted (a : ℕ → ℂ) (ha : Summable a) (α : AddCircle (1 : ℝ)) :
    Summable (fun n => ‖a n * fourier (n : ℤ) α‖) := by
  simpa only [norm_term] using ha.norm

lemma expand_triple (a b c : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (N : ℕ) (α : AddCircle (1 : ℝ)) :
    expSum a α * expSum b α * expSum c α * fourier (-(N : ℤ)) α =
      ∑' t : (ℕ × ℕ) × ℕ,
        (a t.1.1 * b t.1.2 * c t.2) *
          fourier ((t.1.1 : ℤ) + (t.1.2 : ℤ) + (t.2 : ℤ) - (N : ℤ)) α := by
  have ha' := summable_twisted a ha α
  have hb' := summable_twisted b hb α
  have hc' := summable_twisted c hc α
  have hab' := ha'.mul_norm hb'
  have habc' := hab'.mul_norm hc'
  unfold expSum
  rw [tsum_mul_tsum_of_summable_norm ha' hb',
    tsum_mul_tsum_of_summable_norm hab' hc', ← habc'.of_norm.tsum_mul_right]
  apply tsum_congr
  intro t
  simp only [sub_eq_add_neg, fourier_add]
  ring

theorem weighted_ternary_counting (a b c : ℕ → ℂ) (ha : Summable a)
    (hb : Summable b) (hc : Summable c) (N : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      expSum a α * expSum b α * expSum c α * fourier (-(N : ℤ)) α
        ∂AddCircle.haarAddCircle) = tripleCount a b c N := by
  classical
  let coeff : (ℕ × ℕ) × ℕ → ℂ := fun t => a t.1.1 * b t.1.2 * c t.2
  let freq : (ℕ × ℕ) × ℕ → ℤ :=
    fun t => (t.1.1 : ℤ) + (t.1.2 : ℤ) + (t.2 : ℤ) - (N : ℤ)
  let F : ((ℕ × ℕ) × ℕ) → AddCircle (1 : ℝ) → ℂ :=
    fun t α => coeff t * fourier (freq t) α
  have hs : Summable (fun t => ‖coeff t‖) := (ha.norm.mul_norm hb.norm).mul_norm hc.norm
  have hi : ∀ t, Integrable (F t) AddCircle.haarAddCircle := by
    intro t
    simpa only [F, smul_eq_mul, mul_comm] using
      (integrable_const (coeff t)).fourier_smul (freq t)
  have hns : Summable (fun t => ∫ α : AddCircle (1 : ℝ), ‖F t α‖
      ∂AddCircle.haarAddCircle) := by
    simp_rw [F, norm_term, integral_const]
    simpa [Measure.real] using hs
  have hterm (t : (ℕ × ℕ) × ℕ) :
      (∫ α : AddCircle (1 : ℝ), F t α ∂AddCircle.haarAddCircle) =
        if t.1.1 + t.1.2 + t.2 = N then coeff t else 0 := by
    rw [show F t = (fun α => coeff t * fourier (freq t) α) from rfl,
      integral_const_mul, integral_character]
    have heq : freq t = 0 ↔ t.1.1 + t.1.2 + t.2 = N := by
      dsimp [freq]
      omega
    simp [heq]
  calc
    _ = ∫ α : AddCircle (1 : ℝ), ∑' t, F t α ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (expand_triple a b c ha hb hc N)
    _ = ∑' t, ∫ α : AddCircle (1 : ℝ), F t α ∂AddCircle.haarAddCircle :=
      (integral_tsum_of_summable_integral_norm hi hns).symm
    _ = ∑ t ∈ tripleIndices N, coeff t := by
      simp_rw [hterm]
      rw [tsum_eq_sum (s := tripleIndices N)]
      · apply Finset.sum_congr rfl
        intro t ht
        simp [(mem_tripleIndices t N).mp ht]
      · intro t ht
        simp [show t.1.1 + t.1.2 + t.2 ≠ N from fun h => ht ((mem_tripleIndices t N).mpr h)]
    _ = tripleCount a b c N := rfl

end Helfgott

theorem solution (a b c : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (N : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      Helfgott.expSum a α * Helfgott.expSum b α * Helfgott.expSum c α * fourier (-(N : ℤ)) α
        ∂AddCircle.haarAddCircle) = Helfgott.tripleCount a b c N :=
  Helfgott.weighted_ternary_counting a b c ha hb hc N

#print axioms solution
