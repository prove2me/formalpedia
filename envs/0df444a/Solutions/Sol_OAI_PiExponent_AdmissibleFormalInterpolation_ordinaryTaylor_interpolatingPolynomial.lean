-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_interpolatingPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:03:21.756168+00:00
-- url     : https://prove2.me/submissions/4adaefbf-a15b-41fe-878e-a737d045331d

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_ordinaryTaylor_coefficient_functionals_linearIndependent

open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
# Interpolating polynomials for ordinary multivariate Taylor coefficient functionals

For a centre `c` and an exponent `e`, let `φ_{c,e}(P) = [X^e] P(X + c)` be the
ordinary multivariate Taylor coefficient functional.  If the centre–exponent
pairs of a finite family are pairwise distinct, then for every index `x` there
is a polynomial `p` which is a unit at `x` and vanishes at all other functionals:
`φ_y(p) = 1` for `y = x` and `φ_y(p) = 0` otherwise.

The proof is an abstract linear-algebra argument.  The family of functionals is
linearly independent (this is the companion theorem
`ordinaryTaylor_coefficient_functionals_linearIndependent`).  Write
`T(v) = (φ_y(v))_y` for the evaluation map into the finite product `ι → ℂ`.
We claim `T` is surjective.  Otherwise its range is a proper subspace, so there
is a nonzero linear functional `g` on `ι → ℂ` vanishing on the range.  Expanding
`g` in the standard coordinates of `ι → ℂ` gives a nontrivial linear relation
among the `φ_y`, contradicting their linear independence.  Surjectivity applied
to the standard basis vector at `x` then yields the desired interpolating
polynomial.
-/

noncomputable section

open scoped BigOperators

/-- The standard basis vector `Pi.single y a` is the scalar multiple `a • Pi.single y 1`. -/
lemma smul_single_eq {ι : Type*} [DecidableEq ι] (y : ι) (a : ℂ) :
    Pi.single y a = a • Pi.single y (1 : ℂ) := by
  funext z
  simp [Pi.single_apply, smul_eq_mul]

/-- A linear functional on a finite product of copies of `ℂ` is the sum of its
coordinates: `g h = ∑ y, g (Pi.single y 1) * h y`. -/
lemma eval_eq_sum_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℂ) →ₗ[ℂ] ℂ) (h : ι → ℂ) :
    g h = ∑ y, g (Pi.single y 1) * h y := by
  conv_lhs => rw [← LinearMap.sum_single_apply (fun _ => ℂ) h]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_single_eq, map_smul, smul_eq_mul, mul_comm]

/-- Every linear functional on a finite product of copies of `ℂ` is a linear
combination of the coordinate projections. -/
lemma linearMap_pi_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℂ) →ₗ[ℂ] ℂ) :
    g = ∑ y, g (Pi.single y 1) • LinearMap.proj y := by
  apply LinearMap.ext
  intro h
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  exact eval_eq_sum_coord g h

/-- If a finite family of linear functionals on a vector space over `ℂ` is
linearly independent, then the associated evaluation map is surjective.  In
particular, for every index `x` there is a vector on which the `x`-th functional
takes the value `1` and all other functionals vanish. -/
lemma exists_interpolating_of_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → V →ₗ[ℂ] ℂ)
    (hli : LinearIndependent ℂ ψ) (x : ι) :
    ∃ v : V, ∀ y : ι, ψ y v = if y = x then 1 else 0 := by
  classical
  let T : V →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun v => fun y => ψ y v
      map_add' := by intro a b; funext y; simp
      map_smul' := by intro r a; funext y; simp }
  -- a functional vanishing on the range of `T` must be the zero functional
  have key : ∀ g : (ι → ℂ) →ₗ[ℂ] ℂ, (∀ v, g (T v) = 0) → g = 0 := by
    intro g hg
    have hrel : ∑ y, g (Pi.single y 1) • ψ y = 0 := by
      apply LinearMap.ext
      intro v
      rw [LinearMap.sum_apply, LinearMap.zero_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      have h1 : (∑ y, g (Pi.single y 1) * (ψ y) v) = g (T v) :=
        (eval_eq_sum_coord g (T v)).symm
      rw [h1, hg v]
    have hcoef : ∀ y, g (Pi.single y 1) = 0 :=
      (Fintype.linearIndependent_iff.mp hli) (fun y => g (Pi.single y 1)) hrel
    rw [linearMap_pi_eq_sum g]
    simp [hcoef]
  -- hence `T` is surjective
  have hsurj : Function.Surjective T := by
    intro w
    by_contra hw
    have hne : LinearMap.range T ≠ ⊤ := by
      intro htop
      exact hw (LinearMap.range_eq_top.mp htop w)
    have hlt : LinearMap.range T < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨g, hgne, hgker⟩ :=
      Submodule.exists_le_ker_of_lt_top (LinearMap.range T) hlt
    exact hgne (key g (fun v => LinearMap.mem_ker.mp (hgker (LinearMap.mem_range_self T v))))
  obtain ⟨v, hv⟩ := hsurj (Pi.single x 1)
  refine ⟨v, fun y => ?_⟩
  have h := congr_fun hv y
  simpa [T, Pi.single_apply] using h

/-- **Interpolating polynomials for distinct ordinary Taylor coefficient
functionals.**  Given pairwise distinct centre–exponent pairs
`(center x, exponent x)`, for every `x` there is a polynomial `p` with
`[X^{exponent y}] p(X + center y) = 1` if `y = x` and `0` otherwise. -/
theorem solution {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin (m + 1) → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (center x, exponent x)))
    (x : ι) :
    ∃ p : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ y : ι,
        (((MvPowerSeries.coeff (exponent y)).comp
          (MvPolynomial.aeval (fun i =>
            MvPowerSeries.C (center y i) + MvPowerSeries.X i)).toLinearMap) p) =
          if y = x then 1 else 0 := by
  classical
  have hli : LinearIndependent ℂ
      (fun y => (MvPowerSeries.coeff (exponent y)).comp
        (MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center y i) + MvPowerSeries.X i)).toLinearMap) :=
    ordinaryTaylor_coefficient_functionals_linearIndependent center exponent hindex
  exact exists_interpolating_of_linearIndependent _ hli x
