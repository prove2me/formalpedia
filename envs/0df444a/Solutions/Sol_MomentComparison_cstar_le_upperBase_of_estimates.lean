-- Prove2me | solution 1 for MomentComparison.cstar_le_upperBase_of_estimates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:34.100851+00:00
-- url     : https://prove2.me/submissions/5e6f162d-ccdb-4cf6-9704-35b35e87d951

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
public import Theorems.Thm_MomentComparison_cstar_le_inf_of_reverse
public import Theorems.Thm_MomentComparison_reverse_moment_comparison_of_polynomial_growth
public import Theorems.Thm_MomentComparison_complexNoise_one_ofReal
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_exists_noise_polynomial
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
    (hHyper : ∀ p : ℝ, 2 < p → ∀ (n : ℕ) (f : Cube n → ℂ) (w : ℂ),
      inLens p w → complexMomentNorm p (complexNoise w f) ≤
        complexMomentNorm (p / (p - 1)) f)
    (hGrowth : ∀ p : ℝ, 2 < p → ∀ (d : ℕ) (P : Polynomial ℂ), P.natDegree ≤ d →
      ∀ M : ℝ, 0 ≤ M → (∀ w, inLens p w → ‖P.eval w‖ ≤ M) →
        ‖P.eval 1‖ ≤ lensFactor p ^ d * M) :
    Cstar ≤ upperBase := by
  change Cstar ≤ sInf ((fun p => lensFactor p ^ (p / (2 * (p - 2)))) '' Set.Ioi 2)
  apply cstar_le_inf_of_reverse
  · intro p hp
    have h := hGrowth p hp 1 1 (by simp) 1 zero_le_one (by simp)
    have h' : 1 ≤ lensFactor p := by simpa using h
    exact zero_lt_one.trans_le h'
  · intro p hp n d f hf
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent (by linarith)).mpr rfl
    exact reverse_moment_comparison_of_polynomial_growth hp hpq (norm_nonneg _)
      (V := {w | inLens p w}) f (fun w => complexNoise w (fun x => (f x : ℂ)))
      (complexNoise_one_ofReal f) (hHyper p hp n _)
      (exists_noise_polynomial f hf) (fun P hP M hM hV => hGrowth p hp d P hP M hM hV)
end MomentComparison
