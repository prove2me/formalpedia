-- Prove2me | solution 1 for MomentComparison.exists_noise_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:41.885458+00:00
-- url     : https://prove2.me/submissions/3d4f82f4-ac87-47ca-88bc-f540501b24e6

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Theorems.Thm_MomentComparison_complexNoise_ofReal
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n d : ℕ} (f : Cube n → ℝ) (hf : HasDegreeLE f d)
    (g : Cube n → ℂ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧ ∀ w : ℂ,
      P.eval w = (∑ x, complexNoise w (fun y => (f y : ℂ)) x * g x) / (2 : ℂ) ^ n := by
  let u : Finset (Finset (Fin n)) := univ.filter (fun s => s.card ≤ d)
  let a : Finset (Fin n) → ℂ := fun s => (cubeAverage (fun y => f y * walsh s y) : ℂ)
  let c : Finset (Fin n) → ℂ := fun s =>
    (∑ x : Cube n, a s * ((walsh s x : ℂ) * g x)) / (2 : ℂ) ^ n
  refine ⟨∑ s ∈ u, Polynomial.monomial s.card (c s), ?_, fun w => ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    exact (Polynomial.natDegree_monomial_le _).trans (mem_filter.mp hs).2
  · simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, complexNoise_ofReal]
    have hzero (s : Finset (Fin n)) (hs : s ∉ u) : a s = 0 := by
      have he := hf s (by simpa [u] using hs)
      change cubeAverage (fun y => f y * walsh s y) = 0 at he
      simp [a, he]
    have htrunc (x : Cube n) :
        (∑ s : Finset (Fin n), a s * (w ^ s.card * (walsh s x : ℂ))) =
          ∑ s ∈ u, a s * (w ^ s.card * (walsh s x : ℂ)) := by
      symm
      apply sum_subset (subset_univ u)
      intro s _ hs
      simp [hzero s hs]
    change (∑ s ∈ u, c s * w ^ s.card) =
      (∑ x : Cube n, (∑ s : Finset (Fin n),
        a s * (w ^ s.card * (walsh s x : ℂ))) * g x) / (2 : ℂ) ^ n
    simp_rw [htrunc, sum_mul, div_eq_mul_inv, c, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    simp only [div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro x _
    ring
end MomentComparison
