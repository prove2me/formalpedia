-- Prove2me | solution 1 for OAI.AbhyankarSathaye.exists_noncoordinate_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:32:23.758452+00:00
-- url     : https://prove2.me/submissions/d2fcaf02-81d5-4f7c-b231-35134ac1e8fb

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Counterexample.lean:L33-L41
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.AbhyankarSathaye.exists_noncoordinate_polynomial.
-- The statement is the platform stub (Theorems.Thm_OAI_AbhyankarSathaye_exists_noncoordinate_polynomial) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_FiberFormulas
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LinearPresentation
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization

-- ---- inline helpers from OAI.AlgebraicGeometry.AbhyankarSathaye.CriticalPoint ----
namespace OAI

/-!
# An explicit critical point away from the zero fiber

At `(h,u,v,w) = (2,0,-1/2,1/2)`, the value of `F` is `-1` and every
partial derivative vanishes. Differentiating the ambient polynomial identity
proves the latter without expanding `F`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

theorem eval_x : eval criticalPoint x = -1 := by
  norm_num [x, u, h, v]

theorem eval_y : eval criticalPoint y = 1 := by
  norm_num [y, u, h, w]

theorem eval_s : eval criticalPoint s = 1 := by
  norm_num [s, S, u, h, v, w]

theorem eval_p : eval criticalPoint p = 2 := by
  norm_num [p, P, eval_x, eval_y, eval_s]

theorem eval_F : eval criticalPoint F = -1 := by
  norm_num [F, h, eval_p]

theorem eval_shiftX : eval criticalPoint shiftX = 0 := by
  norm_num [shiftX, eval_x, eval_s]

theorem eval_shiftY : eval criticalPoint shiftY = 0 := by
  norm_num [shiftY, eval_y, eval_s]

theorem critical_of_ambient_identity {σ B : Type*} [CommRing B]
    (A D E f : MvPolynomial σ B) (point : σ → B)
    (hid : A^2 + D^3 = E*(1+f))
    (hA : eval point A = 0) (hD : eval point D = 0)
    (hE : eval point E = 1) (hf : eval point f = -1) (i : σ) :
    eval point (pderiv i f) = 0 := by
  have hd := congrArg (fun z => eval point (pderiv i z)) hid
  simpa [pderiv_pow, pderiv_mul, hA, hD, hE, hf] using hd.symm

theorem critical_derivatives (i : Fin 4) : eval criticalPoint (pderiv i F) = 0 :=
  critical_of_ambient_identity shiftX shiftY s F criticalPoint ambient
    eval_shiftX eval_shiftY eval_s eval_F i

end AbhyankarSathaye

end

end OAI

-- ---- inline helpers from OAI.AlgebraicGeometry.AbhyankarSathaye.NonCoordinate ----
namespace OAI

/-!
# Critical points obstruct polynomial coordinates

The polynomial chain rule shows that a coordinate polynomial over a nontrivial
commutative ring cannot have a point where every partial derivative vanishes.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

theorem polynomial_chain_rule {σ τ B : Type*} [Fintype σ] [CommRing B]
    (φ : MvPolynomial σ B →ₐ[B] MvPolynomial τ B)
    (f : MvPolynomial σ B) (j : τ) :
    pderiv j (φ f) = ∑ i, φ (pderiv i f) * pderiv j (φ (X i)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [algHom_C]
  | add f g hf hg =>
      simp only [map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f a hf =>
      have hite (p : Prop) [Decidable p] (A D : MvPolynomial τ B) :
          (if p then A+D else A) = A+(if p then D else 0) := by
        split_ifs <;> simp
      simp only [map_mul, pderiv_mul, map_add, hf]
      simp [pderiv_X, Pi.single_apply, apply_ite, add_mul,
        Finset.mul_sum, mul_comm, mul_assoc]
      simp only [hite, Finset.sum_add_distrib]
      simp

theorem no_coordinate_of_critical {σ B : Type*} [Fintype σ] [CommRing B]
    [Nontrivial B] (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) :
    ¬ ∃ (e : MvPolynomial σ B ≃ₐ[B] MvPolynomial σ B) (i : σ), e (X i) = f := by
  rintro ⟨e, i, he⟩
  have hchain := polynomial_chain_rule e.symm.toAlgHom f i
  change pderiv i (e.symm f) =
    ∑ j, e.symm (pderiv j f) * pderiv i (e.symm (X j)) at hchain
  have hinv : e.symm f = X i := by rw [← he, e.symm_apply_apply]
  rw [hinv, pderiv_X_self] at hchain
  have hz := congrArg (fun q => eval point (e q)) hchain
  simp [map_sum, hc] at hz

theorem F_not_coordinate : ¬ ∃ (e : R ≃ₐ[ℂ] R) (i : Fin 4), e (X i) = F :=
  no_coordinate_of_critical F criticalPoint critical_derivatives

end AbhyankarSathaye

end

end OAI

-- ---- inline helpers from OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization ----
namespace OAI

/-!
# Adjoining unused variables

For every `n ≥ 4`, renaming `F` into the first four variables gives a quotient
isomorphic to a polynomial algebra in `n - 1` variables. The extended critical
point still has value `-1` and zero gradient, so the polynomial is not a coordinate.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

theorem extendedPoint_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    extendedPoint hn (fourInclusion hn i) = criticalPoint i := by
  simp [extendedPoint, fourInclusion, i.isLt]

theorem extended_eval {n : ℕ} (hn : 4 ≤ n) (f : R) :
    eval (extendedPoint hn) (rename (fourInclusion hn) f) = eval criticalPoint f := by
  rw [eval_rename]
  have he : extendedPoint hn ∘ fourInclusion hn = criticalPoint := by
    funext i
    exact extendedPoint_original hn i
  rw [he]

theorem extendedF_eval {n : ℕ} (hn : 4 ≤ n) : eval (extendedPoint hn) (extendedF hn) = -1 := by
  rw [extendedF, extended_eval, eval_F]

theorem extendedF_critical {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    eval (extendedPoint hn) (pderiv i (extendedF hn)) = 0 := by
  apply critical_of_ambient_identity
    (rename (fourInclusion hn) shiftX) (rename (fourInclusion hn) shiftY)
    (rename (fourInclusion hn) s) (extendedF hn) (extendedPoint hn)
  · simpa only [extendedF, map_add, map_pow, map_mul, map_one] using
      congrArg (rename (fourInclusion hn)) ambient
  · rw [extended_eval, eval_shiftX]
  · rw [extended_eval, eval_shiftY]
  · rw [extended_eval, eval_s]
  · exact extendedF_eval hn

theorem extendedF_not_coordinate {n : ℕ} (hn : 4 ≤ n) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = extendedF hn :=
  no_coordinate_of_critical (extendedF hn) (extendedPoint hn) (extendedF_critical hn)

end AbhyankarSathaye

end

end OAI

-- ---- inline helpers from OAI.AlgebraicGeometry.AbhyankarSathaye.Counterexample ----
namespace OAI

/-!
# A polynomial hypersurface with a non-coordinate equation

The explicit polynomial `F` has zero fiber isomorphic to affine three-space,
but has a critical point on the fiber of value `-1`, obstructing its being a
polynomial coordinate. Both conclusions persist after adjoining any number
of unused variables.
-/

namespace AbhyankarSathaye

/-- The explicit hypersurface has a polynomial coordinate ring but its defining
polynomial is not a coordinate, in every ambient dimension at least four. -/
theorem counterexample :
    Nonempty ((R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ) ∧
    (∀ index : Fin 4, MvPolynomial.eval criticalPoint (MvPolynomial.pderiv index F) = 0) ∧
    MvPolynomial.eval criticalPoint F = -1 ∧
    (¬ ∃ (equiv : R ≃ₐ[ℂ] R) (index : Fin 4), equiv (MvPolynomial.X index) = F) ∧
    ∀ (dimension : ℕ) (bound : 4 ≤ dimension),
      Nonempty ((MvPolynomial (Fin dimension) ℂ ⧸ Ideal.span {extendedF bound}) ≃ₐ[ℂ]
        MvPolynomial (Fin (dimension - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin dimension) ℂ ≃ₐ[ℂ] MvPolynomial (Fin dimension) ℂ)
        (index : Fin dimension), equiv (MvPolynomial.X index) = extendedF bound :=
  ⟨⟨fiberEquiv⟩, critical_derivatives, eval_F, F_not_coordinate,
    fun _ bound => ⟨⟨extendedFiberEquiv bound⟩, extendedF_not_coordinate bound⟩⟩

end AbhyankarSathaye

end OAI

-- ---- hoisted mission target ----
open OAI OAI.AbhyankarSathaye

theorem solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {F}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
        (index : Fin n), equiv (MvPolynomial.X index) = F :=
  ⟨extendedF hn, counterexample.2.2.2.2 n hn⟩
