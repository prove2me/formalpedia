-- Prove2me | solution 1 for LamLitt.integrality_implies_algebraicity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:19:57.057115+00:00
-- url     : https://prove2.me/submissions/027e6c38-ffba-43c1-8385-5dc6eb5b59af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_coeff_denominator_bound_of_integrality
import Theorems.Thm_LamLitt_isSolutionOfAlgebraicODE_smul_rescale
import Theorems.Thm_LamLitt_integer_coefficients_implies_algebraicity
import Mathlib

set_option autoImplicit false

open PowerSeries

/-!
# Lam–Litt, Problem 1: reduction of "bounded denominators ⇒ algebraic"

Reduction of `LamLitt.integrality_implies_algebraicity` to three lemmas:

* `LamLitt.coeff_denominator_bound_of_integrality` : coefficients in `ℤ[1/N]` plus the ODE give
  a geometric denominator bound `M ^ (k + 1) * a_k ∈ ℤ`;
* `LamLitt.isSolutionOfAlgebraicODE_smul_rescale` : `a • f(b z)` again solves an algebraic ODE;
* `LamLitt.integer_coefficients_implies_algebraicity` : the integer-coefficient case.

The only mathematics done here is the (elementary) descent of algebraicity along
`F(z) = M · f(M z)`.
-/

namespace LamLittAuxM3

/-- Coefficientwise description of `algebraMap ℚ[X] ℚ⟦X⟧`. -/
theorem coeff_algebraMap (P : Polynomial ℚ) (k : ℕ) :
    coeff k (algebraMap (Polynomial ℚ) (PowerSeries ℚ) P) = P.coeff k := by
  rw [PowerSeries.algebraMap_apply']
  simp

/-- The substitution `z ↦ c z` on power series is compatible with the substitution
`P ↦ P(c X)` on polynomials. -/
theorem rescale_comp_algebraMap (c : ℚ) :
    RingHom.comp (algebraMap (Polynomial ℚ) (PowerSeries ℚ))
        (Polynomial.compRingHom (Polynomial.C c * Polynomial.X)) =
      RingHom.comp (rescale c) (algebraMap (Polynomial ℚ) (PowerSeries ℚ)) := by
  refine RingHom.ext fun P => PowerSeries.ext fun k => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, coeff_algebraMap,
    coeff_rescale, Polynomial.comp_C_mul_X_coeff]
  ring

/-- `P ↦ P(c X)` is injective for `c ≠ 0`. -/
theorem compRingHom_injective (c : ℚ) (hc : c ≠ 0) :
    Function.Injective (Polynomial.compRingHom (Polynomial.C c * Polynomial.X) :
      Polynomial ℚ →+* Polynomial ℚ) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  exact (Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hc)).1 hP

/-- Algebraicity over `ℚ[z]` is preserved by `h(z) ↦ h(c z)` for `c ≠ 0`. -/
theorem isAlgebraic_rescale (c : ℚ) (hc : c ≠ 0) (h : PowerSeries ℚ)
    (halg : IsAlgebraic (Polynomial ℚ) h) : IsAlgebraic (Polynomial ℚ) (rescale c h) :=
  halg.ringHom_of_comp_eq (Polynomial.compRingHom (Polynomial.C c * Polynomial.X)) (rescale c)
    (compRingHom_injective c hc) (rescale_comp_algebraMap c)

/-- Algebraicity over `ℚ[z]` is preserved by multiplication by a rational constant. -/
theorem isAlgebraic_smul (r : ℚ) (h : PowerSeries ℚ)
    (halg : IsAlgebraic (Polynomial ℚ) h) : IsAlgebraic (Polynomial ℚ) (r • h) := by
  have hr : r • h = algebraMap (Polynomial ℚ) (PowerSeries ℚ) (Polynomial.C r) * h := by
    ext k
    rw [PowerSeries.algebraMap_apply']
    simp
  rw [hr]
  exact (isAlgebraic_algebraMap _).mul halg

/-- Descent: if `a • h(b z)` is algebraic over `ℚ[z]` with `a, b ≠ 0`, then so is `h`. -/
theorem isAlgebraic_of_smul_rescale (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (h : PowerSeries ℚ)
    (halg : IsAlgebraic (Polynomial ℚ) (a • rescale b h)) : IsAlgebraic (Polynomial ℚ) h := by
  have h1 : h = rescale b⁻¹ (a⁻¹ • (a • rescale b h)) := by
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, rescale_rescale, mul_inv_cancel₀ hb,
      rescale_one, RingHom.id_apply]
  rw [h1]
  exact isAlgebraic_rescale _ (inv_ne_zero hb) _ (isAlgebraic_smul _ _ halg)

end LamLittAuxM3

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    IsAlgebraic (Polynomial ℚ) f := by
  -- Step 1: a geometric denominator bound `M ^ (k + 1) * a_k ∈ ℤ`.
  obtain ⟨M, hM, hbound⟩ := coeff_denominator_bound_of_integrality f g hODE N hN
  have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  -- Step 2: `F(z) = M · f(M z)` solves an algebraic ODE of the same order ...
  obtain ⟨g', hODE'⟩ := isSolutionOfAlgebraicODE_smul_rescale f g hODE (M : ℚ) (M : ℚ) hM0 hM0
  -- ... and has integer coefficients `M ^ (k + 1) * a_k`.
  have hZ : ∀ k : ℕ, ∃ m : ℤ,
      PowerSeries.coeff k ((M : ℚ) • PowerSeries.rescale (M : ℚ) f) = (m : ℚ) := by
    intro k
    obtain ⟨m, hm⟩ := hbound k
    refine ⟨m, ?_⟩
    rw [← hm, PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul, pow_succ]
    ring
  -- Step 3: the integer-coefficient case gives algebraicity of `F`.
  have hF := integer_coefficients_implies_algebraicity _ g' hODE' hZ
  -- Step 4: descend from `F` to `f`.
  exact LamLittAuxM3.isAlgebraic_of_smul_rescale (M : ℚ) (M : ℚ) hM0 hM0 f hF
