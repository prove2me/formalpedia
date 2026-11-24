-- Prove2me | solution 1 for MomentComparison.reverse_moment_comparison_of_polynomial_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:27.424626+00:00
-- url     : https://prove2.me/submissions/989616df-870d-4339-9eae-a7ee2bbffb74

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
public import Theorems.Thm_MomentComparison_realMomentNorm_le_of_pairing
public import Theorems.Thm_MomentComparison_complexMomentNorm_nonneg
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_norm_cubePair_le
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution
    {n d : ℕ} {p q L : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q) (hL : 0 ≤ L)
    {V : Set ℂ} (f : Cube n → ℝ) (F : ℂ → Cube n → ℂ)
    (hFone : ∀ x, F 1 x = (f x : ℂ))
    (hcontract : ∀ w ∈ V, complexMomentNorm p (F w) ≤
      complexMomentNorm q (fun x => (f x : ℂ)))
    (hpoly : ∀ g : Cube n → ℂ, ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧
      ∀ w, P.eval w = (∑ x, F w x * g x) / (2 : ℂ) ^ n)
    (hgrowth : ∀ (P : Polynomial ℂ), P.natDegree ≤ d → ∀ M : ℝ, 0 ≤ M →
      (∀ w ∈ V, ‖P.eval w‖ ≤ M) → ‖P.eval 1‖ ≤ L ^ d * M) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm q (fun x => (f x : ℂ)) := by
  let M := complexMomentNorm q (fun x => (f x : ℂ))
  have hM : 0 ≤ M := complexMomentNorm_nonneg _ _
  apply realMomentNorm_le_of_pairing hp hpq (mul_nonneg (pow_nonneg hL _) hM) f
  intro g
  obtain ⟨P, hdeg, heval⟩ := hpoly g
  have hnorm := complexMomentNorm_nonneg q g
  have hV (w) (hw : w ∈ V) : ‖P.eval w‖ ≤ M * complexMomentNorm q g := by
    rw [heval]
    exact (norm_cubePair_le hpq (F w) g).trans
      (mul_le_mul_of_nonneg_right (hcontract w hw) hnorm)
  have h := hgrowth P hdeg _ (mul_nonneg hM hnorm) hV
  rw [heval, ← mul_assoc] at h
  simpa only [hFone] using h
end MomentComparison
