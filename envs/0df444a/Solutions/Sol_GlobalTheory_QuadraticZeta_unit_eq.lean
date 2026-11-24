-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:45.920803+00:00
-- url     : https://prove2.me/submissions/394a2874-438c-4b55-aa50-213afc7acd41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis_embedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_norm_eq_sq
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
include σ
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (hd : 4 < d) (u : (𝓞 K)ˣ) : u = 1 ∨ u = -1 := by
  obtain ⟨b, t, h0, hr, hi⟩ := exists_basis_embedding h2 hD σ
  have h1 : ‖σ (u : 𝓞 K)‖ ^ 2 = 1 := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (NumberField.Units.norm K u)
    rw [Rat.cast_abs, norm_eq_sq h2 hD σ, abs_of_nonneg (by positivity)] at h
    simpa using h
  have h3 := eq_coord b h0 u
  generalize b.repr u 0 = x, b.repr u 1 = y at h3
  rw [h3, Complex.sq_norm, Complex.normSq_apply] at h1
  simp at h1
  have h4 : (2 * x + y * t) ^ 2 + y ^ 2 * d = 4 := by
    have : (2 * x + y * t : ℝ) ^ 2 + y ^ 2 * d = 4 := by
      rw [← hr, ← hi]
      linear_combination 4 * h1
    exact_mod_cast this
  have hy : y = 0 := by
    by_contra hy
    have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * x + y * t)]
  subst hy
  have hx : x = 1 ∨ x = -1 := Int.isUnit_iff.1 (IsUnit.of_mul_eq_one x (by nlinarith))
  rcases hx with rfl | rfl
  · exact Or.inl (Units.ext (by simpa using h3))
  · exact Or.inr (Units.ext (by simpa using h3))
end GlobalTheory.QuadraticZeta
