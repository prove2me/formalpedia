-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/34d1cb22-f3a9-5e01-8982-c86bf4bd0b64

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

private theorem linearSystem_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (y : ℝ → Fin n → ℂ)
    (hy : ∀ t, HasDerivAt y (M.mulVec (y t)) t) (h0 : y 0 = 0) : y = 0 := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap M.mulVecLin
  have hLfun : (fun z : Fin n → ℂ => M.mulVec z) = ⇑L := by
    funext z
    simp [L]
  have hL : ∀ t : ℝ,
      LipschitzOnWith ‖L‖₊ (fun z : Fin n → ℂ => M.mulVec z) (Set.univ : Set (Fin n → ℂ)) := by
    intro _
    rw [hLfun]
    exact L.lipschitz.lipschitzOnWith
  refine ODE_solution_unique_univ (v := fun _ z => M.mulVec z) (s := fun _ => Set.univ) (t₀ := (0 : ℝ))
    hL (fun t => ⟨hy t, Set.mem_univ _⟩) (fun t => ⟨?_, Set.mem_univ _⟩) (by simp [h0])
  simp

private theorem span_eq_top_of_separating {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] (Φ : Set (Module.Dual ℂ Y)) (hΦ : ∀ v : Y, (∀ φ ∈ Φ, φ v = 0) → v = 0) :
    Submodule.span ℂ Φ = ⊤ := by
  have hco : (Submodule.span ℂ Φ).dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact hΦ v fun φ hφ => hv φ (Submodule.subset_span hφ)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ Φ)
  rw [hco, Submodule.dualAnnihilator_bot] at h
  exact h.symm

private theorem hasDerivAt_dual_of_separating {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] (Φ : Set (Module.Dual ℂ Y)) (hΦ : ∀ v : Y, (∀ φ ∈ Φ, φ v = 0) → v = 0)
    (x : ℝ → Y) (w : Y) (t : ℝ) (h : ∀ φ ∈ Φ, HasDerivAt (fun u => φ (x u)) (φ w) t)
    (ψ : Module.Dual ℂ Y) : HasDerivAt (fun u => ψ (x u)) (ψ w) t := by
  have hψ : ψ ∈ Submodule.span ℂ Φ := by
    rw [span_eq_top_of_separating Φ hΦ]
    exact Submodule.mem_top
  induction hψ using Submodule.span_induction with
  | mem φ hφ => exact h φ hφ
  | zero => simpa using hasDerivAt_const t (0 : ℂ)
  | add φ₁ φ₂ _ _ h₁ h₂ => simpa using h₁.fun_add h₂
  | smul c φ _ hφ => simpa using hφ.const_mul c

private theorem mem_of_hasDerivAt_of_mapsTo {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] (Γ : Submodule ℂ Y) (D : Y →ₗ[ℂ] Y) (hD : ∀ z ∈ Γ, D z ∈ Γ) (x : ℝ → Y)
    (hx : ∀ (φ : Module.Dual ℂ Y) (t : ℝ), HasDerivAt (fun u => φ (x u)) (φ (D (x t))) t)
    (h0 : x 0 ∈ Γ) (t : ℝ) : x t ∈ Γ := by
  let Dq : (Y ⧸ Γ) →ₗ[ℂ] (Y ⧸ Γ) := Γ.mapQ Γ D fun z hz => hD z hz
  let b := Module.finBasis ℂ (Y ⧸ Γ)
  let N := LinearMap.toMatrix b b Dq
  let y : ℝ → Fin (Module.finrank ℂ (Y ⧸ Γ)) → ℂ := fun u => b.repr (Γ.mkQ (x u))
  have hy : ∀ u, HasDerivAt y (N.mulVec (y u)) u := by
    intro u
    rw [hasDerivAt_pi]
    intro i
    have h1 := hx ((b.coord i).comp Γ.mkQ) u
    have h2 : N.mulVec (y u) i = ((b.coord i).comp Γ.mkQ) (D (x u)) := by
      simp only [y, N]
      rw [LinearMap.toMatrix_mulVec_repr]
      simp [Dq, Submodule.mapQ_apply]
    rw [h2]
    exact h1
  have hy0 : y 0 = 0 := by
    simp [y, h0]
  have hz := linearSystem_eq_zero N y hy hy0
  have h3 : b.repr (Γ.mkQ (x t)) = 0 := by
    ext i
    exact congrFun (congrFun hz t) i
  have h4 : Γ.mkQ (x t) = 0 := b.repr.map_eq_zero_iff.mp h3
  exact (Submodule.Quotient.mk_eq_zero Γ).1 h4

private theorem hasDerivAt_eval_of_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : MvPolynomial ι ℂ) (v : ℝ → ι → ℂ) (v' : ι → ℂ) (t : ℝ)
    (hv : ∀ i, HasDerivAt (fun u => v u i) (v' i) t) :
    HasDerivAt (fun u => MvPolynomial.eval (v u) q)
      (∑ i, MvPolynomial.eval (v t) (MvPolynomial.pderiv i q) * v' i) t := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p₁ p₂ h₁ h₂ => simpa [Finset.sum_add_distrib, add_mul] using h₁.fun_add h₂
  | mul_X p i h =>
    have hfun : (fun u => MvPolynomial.eval (v u) (p * MvPolynomial.X i)) =
        fun u => MvPolynomial.eval (v u) p * v u i := by
      funext u
      simp
    have hterm : ∀ k, MvPolynomial.eval (v t) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) * v' k =
        MvPolynomial.eval (v t) (MvPolynomial.pderiv k p) * v' k * v t i +
          if k = i then MvPolynomial.eval (v t) p * v' i else 0 := by
      intro k
      by_cases hki : k = i
      · subst hki
        simp
        ring
      · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hki), hki]
        ring
    have hval : (∑ k, MvPolynomial.eval (v t) (MvPolynomial.pderiv k (p * MvPolynomial.X i)) * v' k) =
        (∑ k, MvPolynomial.eval (v t) (MvPolynomial.pderiv k p) * v' k) * v t i +
          MvPolynomial.eval (v t) p * v' i := by
      rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib]
      simp [Finset.sum_mul]
    rw [hfun, hval]
    exact h.mul (hv i)

open MvPolynomial

noncomputable section

namespace AxisHarmonics

private def axisA (j : Fin 3) : Fin 3 := ![1, 0, 0] j
private def axisB (j : Fin 3) : Fin 3 := ![2, 2, 1] j

private lemma axisA_ne_axisB (j : Fin 3) : axisA j ≠ axisB j := by
  fin_cases j <;> decide
private lemma axisA_ne (j : Fin 3) : axisA j ≠ j := by
  fin_cases j <;> decide
private lemma axisB_ne (j : Fin 3) : axisB j ≠ j := by
  fin_cases j <;> decide

section laplacian
variable {S : Type*} [CommRing S]

private def lapL : MvPolynomial (Fin 3) S →ₗ[S] MvPolynomial (Fin 3) S :=
  ∑ i : Fin 3, ((pderiv i : Derivation S _ _) : MvPolynomial (Fin 3) S →ₗ[S] MvPolynomial (Fin 3) S) ∘ₗ
    ((pderiv i : Derivation S _ _) : MvPolynomial (Fin 3) S →ₗ[S] MvPolynomial (Fin 3) S)

private lemma lapL_apply (q : MvPolynomial (Fin 3) S) :
    lapL q = ∑ i : Fin 3, pderiv i (pderiv i q) := by
  simp [lapL, LinearMap.sum_apply]

private def gradPair (f g : MvPolynomial (Fin 3) S) : MvPolynomial (Fin 3) S :=
  ∑ i : Fin 3, pderiv i f * pderiv i g

private lemma gradPair_comm (f g : MvPolynomial (Fin 3) S) : gradPair f g = gradPair g f := by
  simp only [gradPair, mul_comm]

private lemma lapL_mul (f g : MvPolynomial (Fin 3) S) :
    lapL (f * g) = f * lapL g + 2 * gradPair f g + g * lapL f := by
  simp only [lapL_apply, gradPair, Fin.sum_univ_three, pderiv_mul, map_add]
  ring

private lemma gradPair_pow_left (f g : MvPolynomial (Fin 3) S) (n : ℕ) :
    gradPair (f ^ n) g = n * f ^ (n - 1) * gradPair f g := by
  simp only [gradPair, Fin.sum_univ_three, pderiv_pow]
  ring

private lemma lapL_pow_eq_zero {f : MvPolynomial (Fin 3) S} (h1 : lapL f = 0) (h2 : gradPair f f = 0)
    (n : ℕ) : lapL (f ^ n) = 0 := by
  induction n with
  | zero => simp [lapL_apply]
  | succ n ih =>
    rw [pow_succ, lapL_mul, ih, h1, gradPair_pow_left, h2]
    ring

private lemma lapL_X (i : Fin 3) : lapL (X i : MvPolynomial (Fin 3) S) = 0 := by
  fin_cases i <;> simp [lapL_apply, Fin.sum_univ_three, pderiv_X]

private lemma pderiv_two (i : Fin 3) : pderiv i (2 : MvPolynomial (Fin 3) S) = 0 := by
  simpa using (pderiv i : Derivation S (MvPolynomial (Fin 3) S) (MvPolynomial (Fin 3) S)).map_natCast 2

end laplacian

section chainRule
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {τ : Type*} [Fintype τ] [DecidableEq τ]

private lemma pderiv_aeval (g : τ → MvPolynomial (Fin 3) S) (Ψ : MvPolynomial τ R) (i : Fin 3) :
    pderiv i (aeval g Ψ) = ∑ k, aeval g (pderiv k Ψ) * pderiv i (g k) := by
  induction Ψ using MvPolynomial.induction_on with
  | C c =>
    simp [IsScalarTower.algebraMap_apply R S (MvPolynomial (Fin 3) S)]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k₀ hp =>
    simp only [map_mul, aeval_X, pderiv_mul, hp, pderiv_X, map_add, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    simp only [Pi.single_apply, apply_ite (aeval g), map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by ring)

private lemma lapL_aeval (g : τ → MvPolynomial (Fin 3) S) (Ψ : MvPolynomial τ R) :
    lapL (aeval g Ψ) =
      (∑ k, ∑ l, aeval g (pderiv l (pderiv k Ψ)) * gradPair (g l) (g k)) +
        ∑ k, aeval g (pderiv k Ψ) * lapL (g k) := by
  simp only [lapL_apply, gradPair, pderiv_aeval, pderiv_mul, map_sum]
  simp only [Fin.sum_univ_three, Finset.sum_add_distrib, Finset.sum_mul, mul_add]
  simp only [mul_assoc]

end chainRule

private def radialOp (Ψ : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  pderiv 0 (pderiv 0 Ψ) + 4 * (X 1 * pderiv 1 (pderiv 1 Ψ) + pderiv 1 Ψ)

private def planeRadiusSq (j : Fin 3) : MvPolynomial (Fin 3) ℂ := X (axisA j) ^ 2 + X (axisB j) ^ 2

private def axisSubst (j : Fin 3) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![X j, planeRadiusSq j]

private lemma gradPair_X_X (j : Fin 3) : gradPair (X j : MvPolynomial (Fin 3) ℂ) (X j) = 1 := by
  fin_cases j <;> simp [gradPair, pderiv_X, Pi.single_apply]

private lemma gradPair_X_radius (j : Fin 3) : gradPair (X j) (planeRadiusSq j) = 0 := by
  fin_cases j <;> simp [gradPair, planeRadiusSq, axisA, axisB, pderiv_X, Pi.single_apply]

private lemma gradPair_radius_radius (j : Fin 3) :
    gradPair (planeRadiusSq j) (planeRadiusSq j) = 4 * planeRadiusSq j := by
  fin_cases j <;> simp [gradPair, planeRadiusSq, axisA, axisB, Fin.sum_univ_three, pderiv_X, Pi.single_apply] <;> ring

private lemma lapL_radius (j : Fin 3) : lapL (planeRadiusSq j) = 4 := by
  fin_cases j <;> simp [lapL_apply, planeRadiusSq, axisA, axisB, Fin.sum_univ_three, pderiv_X, pderiv_two] <;> ring

private lemma lapL_axisSubst (j : Fin 3) (Ψ : MvPolynomial (Fin 2) ℂ) :
    lapL (axisSubst j Ψ) = axisSubst j (radialOp Ψ) := by
  unfold axisSubst
  rw [lapL_aeval]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, gradPair_X_X,
    gradPair_X_radius, gradPair_comm (planeRadiusSq j) (X j), gradPair_radius_radius, lapL_X, lapL_radius,
    radialOp, map_add, map_mul, aeval_X, map_ofNat]
  ring

private abbrev CoeffP := MvPolynomial (Fin 3) ℂ
private abbrev OuterP := MvPolynomial (Fin 3) CoeffP

private def pairT : OuterP := ∑ i : Fin 3, C (X i : CoeffP) * X i
private def innerS : OuterP := ∑ i : Fin 3, C (X i : CoeffP) ^ 2
private def outerU : OuterP := ∑ i : Fin 3, (X i : OuterP) ^ 2
private def pairG : OuterP := innerS * outerU - pairT ^ 2

private def pairSubst : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] OuterP := aeval ![pairT, pairG]

private lemma pderiv_C_outer (i : Fin 3) (p : CoeffP) : pderiv i (C p : OuterP) = 0 := pderiv_C

private lemma gradPair_pairT_pairT : gradPair pairT pairT = innerS := by
  simp only [gradPair, pairT, innerS, Fin.sum_univ_three, map_add, pderiv_mul, pderiv_C_outer, pderiv_X,
    Pi.single_apply]
  simp
  ring

private lemma lapL_pairT : lapL pairT = 0 := by
  simp only [lapL_apply, pairT, Fin.sum_univ_three, map_add, pderiv_mul, pderiv_C_outer, pderiv_X,
    Pi.single_apply]
  simp

private lemma gradPair_pairT_pairG : gradPair pairT pairG = 0 := by
  simp only [gradPair, pairT, pairG, innerS, outerU, Fin.sum_univ_three, map_add, map_sub, pderiv_mul,
    pderiv_pow, pderiv_C_outer, pderiv_X, Pi.single_apply]
  simp
  ring

private lemma gradPair_pairG_pairG : gradPair pairG pairG = 4 * innerS * pairG := by
  simp only [gradPair, pairT, pairG, innerS, outerU, Fin.sum_univ_three, map_add, map_sub, pderiv_mul,
    pderiv_pow, pderiv_C_outer, pderiv_X, Pi.single_apply]
  simp
  ring

private lemma lapL_pairG : lapL pairG = 4 * innerS := by
  simp only [lapL_apply, pairT, pairG, innerS, outerU, Fin.sum_univ_three, map_add, map_sub, pderiv_mul,
    pderiv_pow, pderiv_C_outer, pderiv_X, Pi.single_apply]
  simp [pderiv_two]
  ring

private lemma lapL_pairSubst (Ψ : MvPolynomial (Fin 2) ℂ) :
    lapL (pairSubst Ψ) = innerS * pairSubst (radialOp Ψ) := by
  unfold pairSubst
  rw [lapL_aeval]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    gradPair_pairT_pairT, gradPair_pairT_pairG, gradPair_comm pairG pairT, gradPair_pairG_pairG, lapL_pairT,
    lapL_pairG, radialOp, map_add, map_mul, aeval_X, map_ofNat]
  ring

private def axisExponent (j : Fin 3) (e : Fin 2 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single j (e 0) + Finsupp.single (axisA j) (2 * e 1)

private lemma axisExponent_injective (j : Fin 3) : Function.Injective (axisExponent j) := by
  intro e₁ e₂ h
  have h0 := DFunLike.congr_fun h j
  have h1 := DFunLike.congr_fun h (axisA j)
  simp only [axisExponent, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (axisA_ne j),
    Finsupp.single_eq_of_ne (axisA_ne j).symm] at h0 h1
  ext i
  fin_cases i <;> simp <;> omega

private lemma aeval_X_X_sq_monomial (j : Fin 3) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    aeval ![X j, X (axisA j) ^ 2] (monomial e c) = (monomial (axisExponent j e) c : CoeffP) := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← pow_mul, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, algebraMap_eq, C_mul_monomial, one_mul,
    mul_one]
  rfl

private lemma aeval_X_X_sq_injective (j : Fin 3) :
    Function.Injective (aeval ![X j, X (axisA j) ^ 2] : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoeffP) := by
  refine (injective_iff_map_eq_zero _).mpr (fun Ψ hΨ => ?_)
  ext e₀
  have hcoeff : coeff (axisExponent j e₀) (aeval ![X j, X (axisA j) ^ 2] Ψ) = coeff e₀ Ψ := by
    conv_lhs => rw [Ψ.as_sum, map_sum]
    simp only [aeval_X_X_sq_monomial, coeff_sum, coeff_monomial, (axisExponent_injective j).eq_iff,
      Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
    split_ifs with h
    · exact h.symm
    · rfl
  rw [hΨ, coeff_zero] at hcoeff
  rw [coeff_zero]
  exact hcoeff.symm

private def killB (j : Fin 3) : CoeffP →ₐ[ℂ] CoeffP := aeval (fun i => if i = axisB j then 0 else X i)

private lemma killB_axisSubst (j : Fin 3) (Ψ : MvPolynomial (Fin 2) ℂ) :
    killB j (axisSubst j Ψ) = aeval ![X j, X (axisA j) ^ 2] Ψ := by
  unfold killB axisSubst
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp [planeRadiusSq, (axisB_ne j).symm, axisA_ne_axisB j]

private lemma axisSubst_injective (j : Fin 3) : Function.Injective (axisSubst j) := by
  intro Ψ₁ Ψ₂ h
  apply aeval_X_X_sq_injective j
  rw [← killB_axisSubst, ← killB_axisSubst, h]

private def rotDeriv (u v : Fin 3) : Derivation ℂ CoeffP CoeffP :=
  (X v : CoeffP) • (pderiv u : Derivation ℂ CoeffP CoeffP) - (X u : CoeffP) • (pderiv v : Derivation ℂ CoeffP CoeffP)

private lemma rotDeriv_apply (u v : Fin 3) (q : CoeffP) :
    rotDeriv u v q = X v * pderiv u q - X u * pderiv v q := by
  simp [rotDeriv, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

private lemma rotDeriv_X (u v i : Fin 3) :
    rotDeriv u v (X i) = (if i = u then X v else 0) - (if i = v then X u else 0) := by
  rw [rotDeriv_apply]
  by_cases hu : i = u <;> by_cases hv : i = v <;> simp [hu, hv, pderiv_X, Pi.single_apply, eq_comm]

private lemma bracket_apply_of_gen {D₁ D₂ D₃ : Derivation ℂ CoeffP CoeffP}
    (h : ∀ i : Fin 3, D₁ (D₂ (X i)) - D₂ (D₁ (X i)) = D₃ (X i)) (q : CoeffP) :
    D₁ (D₂ q) - D₂ (D₁ q) = D₃ q := by
  have hD : ⁅D₁, D₂⁆ = D₃ := derivation_ext (fun i => by rw [Derivation.commutator_apply]; exact h i)
  simpa [Derivation.commutator_apply] using Derivation.congr_fun hD q

private lemma rotDeriv_comm_01_02 (q : CoeffP) :
    rotDeriv 0 1 (rotDeriv 0 2 q) - rotDeriv 0 2 (rotDeriv 0 1 q) = rotDeriv 1 2 q :=
  bracket_apply_of_gen (fun i => by fin_cases i <;> simp [rotDeriv_X]) q

private lemma rotDeriv_comm_01_12 (q : CoeffP) :
    rotDeriv 0 1 (rotDeriv 1 2 q) - rotDeriv 1 2 (rotDeriv 0 1 q) = - rotDeriv 0 2 q := by
  have h := bracket_apply_of_gen (D₁ := rotDeriv 0 1) (D₂ := rotDeriv 1 2) (D₃ := - rotDeriv 0 2)
    (fun i => by fin_cases i <;> simp [rotDeriv_X]) q
  simpa [Derivation.neg_apply] using h

private lemma rotDeriv_comm_02_12 (q : CoeffP) :
    rotDeriv 0 2 (rotDeriv 1 2 q) - rotDeriv 1 2 (rotDeriv 0 2 q) = rotDeriv 0 1 q :=
  bracket_apply_of_gen (fun i => by fin_cases i <;> simp [rotDeriv_X]) q

private lemma pderiv_pderiv_comm (i k : Fin 3) (q : CoeffP) : pderiv i (pderiv k q) = pderiv k (pderiv i q) := by
  have h := bracket_apply_of_gen (D₁ := pderiv i) (D₂ := pderiv k) (D₃ := 0)
    (fun n => by simp [pderiv_X, Pi.single_apply]; split_ifs <;> simp) q
  rw [Derivation.zero_apply, sub_eq_zero] at h
  exact h

private lemma lapL_pderiv (u : Fin 3) (q : CoeffP) : lapL (pderiv u q) = pderiv u (lapL q) := by
  simp only [lapL_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [pderiv_pderiv_comm i u q, pderiv_pderiv_comm i u (pderiv i q)])

private lemma gradPair_X_left (v : Fin 3) (r : CoeffP) : gradPair (X v) r = pderiv v r := by
  fin_cases v <;> simp [gradPair, Fin.sum_univ_three, pderiv_X]

private lemma degree_sub_single_add_one {d : Fin 3 →₀ ℕ} {u : Fin 3} (hu : d u ≠ 0) :
    (d - Finsupp.single u 1).degree + 1 = d.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [Fin.sum_univ_three, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  fin_cases u <;> simp at hu ⊢ <;> omega

private lemma X_mul_pderiv_monomial_isHomogeneous (u v : Fin 3) (d : Fin 3 →₀ ℕ) (c : ℂ) :
    (X v * pderiv u (monomial d c) : CoeffP).IsHomogeneous d.degree := by
  rw [pderiv_monomial]
  by_cases h : d u = 0
  · rw [h, Nat.cast_zero, mul_zero, monomial_zero, mul_zero]
    exact isHomogeneous_zero _ _ _
  · have h2 := (isHomogeneous_X ℂ v).mul
      (isHomogeneous_monomial (c * (d u : ℂ)) (rfl : (d - Finsupp.single u 1).degree = _))
    rwa [add_comm, degree_sub_single_add_one h] at h2

private lemma rotDeriv_isHomogeneous {q : CoeffP} {n : ℕ} (hq : q.IsHomogeneous n) (u v : Fin 3) :
    (rotDeriv u v q).IsHomogeneous n := by
  rw [rotDeriv_apply, q.as_sum, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsHomogeneous.sum _ _ _ (fun d hd => ?_)
  have hdeg : d.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hd) (hq.coeff_eq_zero hne)
  rw [← hdeg]
  exact (X_mul_pderiv_monomial_isHomogeneous u v d _).sub (X_mul_pderiv_monomial_isHomogeneous v u d _)

private lemma lapL_rotDeriv (u v : Fin 3) (q : CoeffP) : lapL (rotDeriv u v q) = rotDeriv u v (lapL q) := by
  rw [rotDeriv_apply, rotDeriv_apply, map_sub, lapL_mul, lapL_mul, lapL_X, lapL_X, gradPair_X_left,
    gradPair_X_left, lapL_pderiv, lapL_pderiv, pderiv_pderiv_comm v u q]
  ring

private def isotropicForm (j : Fin 3) : CoeffP := X (axisA j) + C Complex.I * X (axisB j)

private lemma lapL_isotropicForm (j : Fin 3) : lapL (isotropicForm j) = 0 := by
  fin_cases j <;> simp [lapL_apply, isotropicForm, axisA, axisB, Fin.sum_univ_three, pderiv_X, Pi.single_apply]

private lemma gradPair_isotropicForm (j : Fin 3) : gradPair (isotropicForm j) (isotropicForm j) = 0 := by
  have hI : (C Complex.I : CoeffP) * C Complex.I = -1 := by
    rw [← C_mul, Complex.I_mul_I, C_neg, C_1]
  fin_cases j <;> simp [gradPair, isotropicForm, axisA, axisB, Fin.sum_univ_three, pderiv_X, Pi.single_apply] <;>
    linear_combination hI

private lemma lapL_isotropicForm_pow (j : Fin 3) (n : ℕ) : lapL (isotropicForm j ^ n) = 0 :=
  lapL_pow_eq_zero (lapL_isotropicForm j) (gradPair_isotropicForm j) n

private lemma isotropicForm_isHomogeneous (j : Fin 3) : (isotropicForm j).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).add ((isHomogeneous_X _ _).C_mul _)

private lemma isotropicForm_ne_zero (j : Fin 3) : isotropicForm j ≠ 0 := by
  intro h
  have h1 := congrArg (eval (Pi.single (axisA j) (1 : ℂ))) h
  simp [isotropicForm, (axisA_ne_axisB j).symm] at h1

private lemma C_I_mul_C_I : (C Complex.I : CoeffP) * C Complex.I = -1 := by
  rw [← C_mul, Complex.I_mul_I, C_neg, C_1]

private lemma isotropic_mul_conj (a b : Fin 3) :
    (X a + C Complex.I * X b : CoeffP) * (X a - C Complex.I * X b) = X a ^ 2 + X b ^ 2 := by
  linear_combination (-(X b : CoeffP) ^ 2) * C_I_mul_C_I

private lemma pow_isotropic_mul_pow (a b : Fin 3) (n : ℕ) :
    (X a + C Complex.I * X b : CoeffP) ^ n * (X a - C Complex.I * X b) ^ n = (X a ^ 2 + X b ^ 2) ^ n := by
  rw [← mul_pow, isotropic_mul_conj]

private def isoChange (j : Fin 3) : CoeffP →ₐ[ℂ] CoeffP :=
  aeval (fun i => if i = axisA j then X (axisA j) + C Complex.I * X (axisB j)
    else if i = axisB j then X (axisA j) - C Complex.I * X (axisB j) else X i)

private def isoChangeInvGen (j : Fin 3) (i : Fin 3) : CoeffP :=
  if i = axisA j then C (1 / 2 : ℂ) * (X (axisA j) + X (axisB j))
  else if i = axisB j then C (-Complex.I / 2) * (X (axisA j) - X (axisB j)) else X i

private def isoChangeInv (j : Fin 3) : CoeffP →ₐ[ℂ] CoeffP := aeval (isoChangeInvGen j)

private lemma isoChangeInvGen_isHomogeneous (j i : Fin 3) : (isoChangeInvGen j i).IsHomogeneous 1 := by
  unfold isoChangeInvGen
  split_ifs
  · exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _
  · exact ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).C_mul _
  · exact isHomogeneous_X _ _

private lemma two_mul_C_half : (2 : CoeffP) * C (1 / 2 : ℂ) = 1 := by
  rw [show (2 : CoeffP) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_1]
  congr 1
  norm_num

private lemma C_negI_half_mul : (C (-Complex.I / 2) : CoeffP) * (2 * C Complex.I) = 1 := by
  rw [show (2 : CoeffP) = C 2 from (map_ofNat C 2).symm, ← C_mul, ← C_mul, ← C_1]
  congr 1
  linear_combination (-1 : ℂ) * Complex.I_mul_I

private lemma C_I_mul_C_negI_half : (C Complex.I : CoeffP) * C (-Complex.I / 2) = C (1 / 2 : ℂ) := by
  rw [← C_mul]
  congr 1
  linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I

private lemma isoChange_isoChangeInv (j : Fin 3) (q : CoeffP) : isoChange j (isoChangeInv j q) = q := by
  have h : (isoChange j).comp (isoChangeInv j) = AlgHom.id ℂ CoeffP := by
    refine algHom_ext (fun i => ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, isoChangeInv, aeval_X, isoChangeInvGen]
    by_cases ha : i = axisA j
    · subst ha
      simp only [if_true, isoChange, map_mul, map_add, aeval_C, aeval_X, (axisA_ne_axisB j).symm, if_false]
      rw [algebraMap_eq]
      linear_combination (X (axisA j) : CoeffP) * two_mul_C_half
    · by_cases hb : i = axisB j
      · subst hb
        simp only [ha, if_false, if_true, isoChange, map_mul, map_sub, aeval_C, aeval_X]
        rw [algebraMap_eq]
        linear_combination (X (axisB j) : CoeffP) * C_negI_half_mul
      · simp only [ha, hb, if_false, isoChange, aeval_X]
  exact AlgHom.congr_fun h q

private lemma C_half_two : (C (1 / 2 : ℂ) : CoeffP) * 2 = 1 := by
  rw [mul_comm]; exact two_mul_C_half

private lemma isoChangeInv_isoChange (j : Fin 3) (q : CoeffP) : isoChangeInv j (isoChange j q) = q := by
  have h : (isoChangeInv j).comp (isoChange j) = AlgHom.id ℂ CoeffP := by
    refine algHom_ext (fun i => ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, isoChange, aeval_X]
    by_cases ha : i = axisA j
    · subst ha
      simp only [if_true, isoChangeInv, map_mul, map_add, aeval_C, aeval_X, isoChangeInvGen,
        (axisA_ne_axisB _).symm, if_false]
      rw [algebraMap_eq]
      linear_combination (X (axisA _) : CoeffP) * C_half_two +
        ((X (axisA _) : CoeffP) - X (axisB _)) * C_I_mul_C_negI_half
    · by_cases hb : i = axisB j
      · subst hb
        simp only [ha, if_false, if_true, isoChangeInv, map_mul, map_sub, aeval_C, aeval_X, isoChangeInvGen]
        rw [algebraMap_eq]
        linear_combination (X (axisB _) : CoeffP) * C_half_two -
          ((X (axisA _) : CoeffP) - X (axisB _)) * C_I_mul_C_negI_half
      · simp only [ha, hb, if_false, isoChangeInv, aeval_X, isoChangeInvGen]
  exact AlgHom.congr_fun h q

private lemma isoChange_injective (j : Fin 3) : Function.Injective (isoChange j) :=
  Function.LeftInverse.injective (isoChangeInv_isoChange j)

private def weightOp (j : Fin 3) : Derivation ℂ CoeffP CoeffP :=
  (-Complex.I) • ((X (axisA j) : CoeffP) • (pderiv (axisA j) : Derivation ℂ CoeffP CoeffP) -
    (X (axisB j) : CoeffP) • (pderiv (axisB j) : Derivation ℂ CoeffP CoeffP))

private lemma weightOp_apply (j : Fin 3) (p : CoeffP) :
    weightOp j p = C (-Complex.I) * (X (axisA j) * pderiv (axisA j) p - X (axisB j) * pderiv (axisB j) p) := by
  simp [weightOp, Derivation.smul_apply, Derivation.sub_apply, smul_eq_mul, smul_eq_C_mul]

private lemma rotDeriv_C (u v : Fin 3) (c : ℂ) : rotDeriv u v (C c) = 0 := by
  simp

private lemma rotDeriv_isoChange_X (j i : Fin 3) :
    rotDeriv (axisA j) (axisB j) (isoChange j (X i)) = isoChange j (weightOp j (X i)) := by
  have hab := axisA_ne_axisB j
  by_cases ha : i = axisA j
  · subst ha
    simp [isoChange, weightOp_apply, pderiv_X, rotDeriv_X, hab, hab.symm, algebraMap_eq, C_neg]
    linear_combination (X (axisB j) : CoeffP) * C_I_mul_C_I
  · by_cases hb : i = axisB j
    · subst hb
      simp [isoChange, weightOp_apply, pderiv_X, rotDeriv_X, hab, hab.symm, algebraMap_eq, C_neg]
      linear_combination (X (axisB j) : CoeffP) * C_I_mul_C_I
    · simp [isoChange, weightOp_apply, pderiv_X, rotDeriv_X, ha, hb]

private lemma rotDeriv_isoChange (j : Fin 3) (p : CoeffP) :
    rotDeriv (axisA j) (axisB j) (isoChange j p) = isoChange j (weightOp j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [isoChange, aeval_C, algebraMap_eq, rotDeriv_C, weightOp_apply, pderiv_C, mul_zero,
      sub_zero, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, map_mul, map_mul, hp, rotDeriv_isoChange_X]

private lemma coeff_X_mul_pderiv (i : Fin 3) (d : Fin 3 →₀ ℕ) (p : CoeffP) :
    coeff d (X i * pderiv i p) = (d i : ℂ) * coeff d p := by
  conv_lhs => rw [p.as_sum, map_sum, Finset.mul_sum]
  simp only [X_mul_pderiv_monomial, nsmul_eq_mul, ← C_eq_coe_nat, coeff_sum, coeff_C_mul, coeff_monomial, mul_ite,
    mul_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with h
  · rw [h, mul_zero]
  · rfl

private lemma coeff_weightOp (j : Fin 3) (d : Fin 3 →₀ ℕ) (p : CoeffP) :
    coeff d (weightOp j p) = -Complex.I * (((d (axisA j) : ℂ) - d (axisB j)) * coeff d p) := by
  rw [weightOp_apply, coeff_C_mul, coeff_sub, coeff_X_mul_pderiv, coeff_X_mul_pderiv]
  ring

private lemma exists_axisSubst_of_rotDeriv_eq_zero (j : Fin 3) {ℓ : ℕ} {q : CoeffP} (hq : q.IsHomogeneous ℓ)
    (hrot : rotDeriv (axisA j) (axisB j) q = 0) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → ℂ) (m n : ι → ℕ),
      (∀ e ∈ s, m e + 2 * n e = ℓ) ∧
      q = axisSubst j (∑ e ∈ s, C (c e) * X 0 ^ m e * X 1 ^ n e) := by
  set r : CoeffP := isoChangeInv j q with hr
  have hqr : q = isoChange j r := (isoChange_isoChangeInv j q).symm
  have hr_hom : r.IsHomogeneous ℓ := by
    have h := hq.aeval (isoChangeInvGen j) (isoChangeInvGen_isHomogeneous j)
    rwa [one_mul] at h
  have hw : weightOp j r = 0 := by
    apply isoChange_injective j
    rw [← rotDeriv_isoChange, ← hqr, hrot, map_zero]
  have hab : ∀ d ∈ r.support, d (axisA j) = d (axisB j) := by
    intro d hd
    have h := congrArg (coeff d) hw
    rw [coeff_weightOp, coeff_zero, mul_eq_zero, mul_eq_zero] at h
    rcases h with h | h | h
    · exact absurd h (neg_ne_zero.mpr Complex.I_ne_zero)
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd h (mem_support_iff.mp hd)
  refine ⟨Fin 3 →₀ ℕ, r.support, fun d => coeff d r, fun d => d j, fun d => d (axisA j), ?_, ?_⟩
  · intro d hd
    have hdeg : d.degree = ℓ := by
      by_contra hne
      exact (mem_support_iff.mp hd) (hr_hom.coeff_eq_zero hne)
    have h2 := hab d hd
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    fin_cases j <;> simp [axisA, axisB] at h2 ⊢ <;> omega
  · rw [hqr]
    conv_lhs => rw [r.as_sum, map_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have h2 := hab d hd
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, map_mul, map_mul,
      map_mul, map_pow, map_pow, map_pow]
    simp only [isoChange, aeval_C, aeval_X, algebraMap_eq, axisSubst, map_mul, map_pow, Matrix.cons_val_zero,
      Matrix.cons_val_one, planeRadiusSq]
    fin_cases j <;> simp [axisA, axisB] at h2 ⊢
    · rw [← h2]
      linear_combination (C (coeff d r) * X 0 ^ d 0 : CoeffP) * pow_isotropic_mul_pow 1 2 (d 1)
    · rw [← h2]
      linear_combination (C (coeff d r) * X 1 ^ d 1 : CoeffP) * pow_isotropic_mul_pow 0 2 (d 0)
    · rw [← h2]
      linear_combination (C (coeff d r) * X 2 ^ d 2 : CoeffP) * pow_isotropic_mul_pow 0 1 (d 0)

private lemma aeval_neg_X_of_isHomogeneous {q : CoeffP} {ℓ : ℕ} (hq : q.IsHomogeneous ℓ) :
    aeval (fun i : Fin 3 => - (X i : CoeffP)) q = (-1) ^ ℓ * q := by
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum, Finset.mul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [hq.degree_eq_sum_deg_support hd, aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod,
    Finset.prod_congr rfl (fun i _ => neg_pow (X i : CoeffP) (d i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  simp only [algebraMap_eq]
  ring

end AxisHarmonics

end

noncomputable section

namespace AxisHarmonics

private def matrixSubst (k : Matrix (Fin 3) (Fin 3) ℝ) : CoeffP →ₐ[ℂ] CoeffP :=
  aeval (fun i : Fin 3 => ∑ l : Fin 3, C ((k l i : ℝ) : ℂ) * X l)

private lemma matrixSubst_X (k : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    matrixSubst k (X i) = ∑ l : Fin 3, C ((k l i : ℝ) : ℂ) * X l := by
  simp [matrixSubst]

private lemma matrixSubst_C (k : Matrix (Fin 3) (Fin 3) ℝ) (c : ℂ) : matrixSubst k (C c) = C c := by
  simp [matrixSubst, algebraMap_eq]

private lemma matrixSubst_mul (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixSubst (x * y) = (matrixSubst x).comp (matrixSubst y) := by
  refine algHom_ext (fun i => ?_)
  rw [AlgHom.comp_apply, matrixSubst_X, matrixSubst_X, map_sum]
  simp only [map_mul, matrixSubst_C, matrixSubst_X, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
  ring

private lemma matrixSubst_one : matrixSubst 1 = AlgHom.id ℂ CoeffP := by
  refine algHom_ext (fun i => ?_)
  rw [matrixSubst_X, AlgHom.id_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private lemma matrixSubst_isHomogeneous (k : Matrix (Fin 3) (Fin 3) ℝ) {q : CoeffP} {n : ℕ}
    (hq : q.IsHomogeneous n) : (matrixSubst k q).IsHomogeneous n := by
  have h := hq.aeval (fun i : Fin 3 => ∑ l : Fin 3, C ((k l i : ℝ) : ℂ) * X l)
    (fun i => IsHomogeneous.sum _ _ _ (fun l _ => (isHomogeneous_X _ _).C_mul _))
  rwa [one_mul] at h

private lemma matrixSubst_neg_one {q : CoeffP} {n : ℕ} (hq : q.IsHomogeneous n) :
    matrixSubst (-1) q = (-1) ^ n * q := by
  rw [← aeval_neg_X_of_isHomogeneous hq]
  refine AlgHom.congr_fun (algHom_ext (fun i => ?_)) q
  rw [matrixSubst_X, aeval_X, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private def planeOf : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

private def planeDeriv (c : Fin 3) : Derivation ℂ CoeffP CoeffP := rotDeriv (planeOf c).1 (planeOf c).2

private lemma rotDeriv_swap (u v : Fin 3) : rotDeriv v u = - rotDeriv u v := by
  refine Derivation.ext (fun q => ?_)
  rw [Derivation.neg_apply, rotDeriv_apply, rotDeriv_apply]; ring

private def axisRot (j : Fin 3) : Derivation ℂ CoeffP CoeffP := rotDeriv (axisA j) (axisB j)
private def liftA (j : Fin 3) : Derivation ℂ CoeffP CoeffP := rotDeriv (axisA j) j
private def liftB (j : Fin 3) : Derivation ℂ CoeffP CoeffP := rotDeriv (axisB j) j

private lemma bracket_liftA_liftB (j : Fin 3) (q : CoeffP) :
    liftA j (liftB j q) - liftB j (liftA j q) = axisRot j q := by
  fin_cases j
  · show rotDeriv 1 0 (rotDeriv 2 0 q) - rotDeriv 2 0 (rotDeriv 1 0 q) = rotDeriv 1 2 q
    rw [rotDeriv_swap 0 1, rotDeriv_swap 0 2]
    simp only [Derivation.neg_apply, map_neg]
    linear_combination rotDeriv_comm_01_02 q
  · show rotDeriv 0 1 (rotDeriv 2 1 q) - rotDeriv 2 1 (rotDeriv 0 1 q) = rotDeriv 0 2 q
    rw [rotDeriv_swap 1 2]
    simp only [Derivation.neg_apply, map_neg]
    linear_combination (-1 : CoeffP) * rotDeriv_comm_01_12 q
  · show rotDeriv 0 2 (rotDeriv 1 2 q) - rotDeriv 1 2 (rotDeriv 0 2 q) = rotDeriv 0 1 q
    exact rotDeriv_comm_02_12 q

private lemma bracket_axisRot_liftA (j : Fin 3) (q : CoeffP) :
    axisRot j (liftA j q) - liftA j (axisRot j q) = liftB j q := by
  fin_cases j
  · show rotDeriv 1 2 (rotDeriv 1 0 q) - rotDeriv 1 0 (rotDeriv 1 2 q) = rotDeriv 2 0 q
    rw [rotDeriv_swap 0 1, rotDeriv_swap 0 2]
    simp only [Derivation.neg_apply, map_neg]
    linear_combination rotDeriv_comm_01_12 q
  · show rotDeriv 0 2 (rotDeriv 0 1 q) - rotDeriv 0 1 (rotDeriv 0 2 q) = rotDeriv 2 1 q
    rw [rotDeriv_swap 1 2]
    simp only [Derivation.neg_apply]
    linear_combination (-1 : CoeffP) * rotDeriv_comm_01_02 q
  · show rotDeriv 0 1 (rotDeriv 0 2 q) - rotDeriv 0 2 (rotDeriv 0 1 q) = rotDeriv 1 2 q
    exact rotDeriv_comm_01_02 q

private lemma bracket_axisRot_liftB (j : Fin 3) (q : CoeffP) :
    axisRot j (liftB j q) - liftB j (axisRot j q) = - liftA j q := by
  fin_cases j
  · show rotDeriv 1 2 (rotDeriv 2 0 q) - rotDeriv 2 0 (rotDeriv 1 2 q) = - rotDeriv 1 0 q
    rw [rotDeriv_swap 0 1, rotDeriv_swap 0 2]
    simp only [Derivation.neg_apply, map_neg]
    linear_combination rotDeriv_comm_02_12 q
  · show rotDeriv 0 2 (rotDeriv 2 1 q) - rotDeriv 2 1 (rotDeriv 0 2 q) = - rotDeriv 0 1 q
    rw [rotDeriv_swap 1 2]
    simp only [Derivation.neg_apply, map_neg]
    linear_combination (-1 : CoeffP) * rotDeriv_comm_02_12 q
  · show rotDeriv 0 1 (rotDeriv 1 2 q) - rotDeriv 1 2 (rotDeriv 0 1 q) = - rotDeriv 0 2 q
    exact rotDeriv_comm_01_12 q

private lemma planeDeriv_eq_axis (j c : Fin 3) :
    planeDeriv c = axisRot j ∨ planeDeriv c = liftA j ∨ planeDeriv c = liftB j ∨
    planeDeriv c = - liftA j ∨ planeDeriv c = - liftB j := by
  fin_cases j <;> fin_cases c <;> simp [planeDeriv, planeOf, axisRot, liftA, liftB, axisA, axisB, rotDeriv_swap 0 1,
    rotDeriv_swap 0 2, rotDeriv_swap 1 2]

private abbrev HomogP (ℓ : ℕ) : Type := MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ

private lemma homogeneousSubmodule_le_restrictTotalDegree (ℓ : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ ≤ MvPolynomial.restrictTotalDegree (Fin 3) ℂ ℓ := by
  intro q hq
  rw [mem_restrictTotalDegree]
  exact ((mem_homogeneousSubmodule _ _).mp hq).totalDegree_le

private scoped instance homogP_finite (ℓ : ℕ) : FiniteDimensional ℂ (HomogP ℓ) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree ℓ)

private def restrictDeg (ℓ : ℕ) (D : Derivation ℂ CoeffP CoeffP)
    (hD : ∀ q : CoeffP, q.IsHomogeneous ℓ → (D q).IsHomogeneous ℓ) : Module.End ℂ (HomogP ℓ) :=
  (D : CoeffP →ₗ[ℂ] CoeffP).restrict (fun q hq =>
    (mem_homogeneousSubmodule _ _).mpr (hD q ((mem_homogeneousSubmodule _ _).mp hq)))

private lemma restrictDeg_coe (ℓ : ℕ) (D : Derivation ℂ CoeffP CoeffP) (hD) (w : HomogP ℓ) :
    ((restrictDeg ℓ D hD w : HomogP ℓ) : CoeffP) = D (w : CoeffP) := rfl

private def planeEnd (ℓ : ℕ) (c : Fin 3) : Module.End ℂ (HomogP ℓ) :=
  restrictDeg ℓ (planeDeriv c) (fun _ hq => rotDeriv_isHomogeneous hq _ _)

private def axisRotEnd (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) :=
  restrictDeg ℓ (axisRot j) (fun _ hq => rotDeriv_isHomogeneous hq _ _)
private def liftAEnd (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) :=
  restrictDeg ℓ (liftA j) (fun _ hq => rotDeriv_isHomogeneous hq _ _)
private def liftBEnd (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) :=
  restrictDeg ℓ (liftB j) (fun _ hq => rotDeriv_isHomogeneous hq _ _)

private lemma planeEnd_eq_axis (ℓ : ℕ) (j c : Fin 3) :
    planeEnd ℓ c = axisRotEnd ℓ j ∨ planeEnd ℓ c = liftAEnd ℓ j ∨ planeEnd ℓ c = liftBEnd ℓ j ∨
    planeEnd ℓ c = - liftAEnd ℓ j ∨ planeEnd ℓ c = - liftBEnd ℓ j := by
  rcases planeDeriv_eq_axis j c with h | h | h | h | h
  · left
    exact LinearMap.ext (fun w => Subtype.ext (by rw [planeEnd, axisRotEnd, restrictDeg_coe, restrictDeg_coe, h]))
  · right; left
    exact LinearMap.ext (fun w => Subtype.ext (by rw [planeEnd, liftAEnd, restrictDeg_coe, restrictDeg_coe, h]))
  · right; right; left
    exact LinearMap.ext (fun w => Subtype.ext (by rw [planeEnd, liftBEnd, restrictDeg_coe, restrictDeg_coe, h]))
  · right; right; right; left
    exact LinearMap.ext (fun w => Subtype.ext (by
      rw [planeEnd, restrictDeg_coe, h, Derivation.neg_apply, LinearMap.neg_apply, Submodule.coe_neg, liftAEnd,
        restrictDeg_coe]))
  · right; right; right; right
    exact LinearMap.ext (fun w => Subtype.ext (by
      rw [planeEnd, restrictDeg_coe, h, Derivation.neg_apply, LinearMap.neg_apply, Submodule.coe_neg, liftBEnd,
        restrictDeg_coe]))

private def tripleH (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) := (2 * Complex.I) • axisRotEnd ℓ j
private def tripleE (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) := liftAEnd ℓ j + Complex.I • liftBEnd ℓ j
private def tripleF (ℓ : ℕ) (j : Fin 3) : Module.End ℂ (HomogP ℓ) := - liftAEnd ℓ j + Complex.I • liftBEnd ℓ j

private lemma liftAEnd_liftBEnd_comm (ℓ : ℕ) (j : Fin 3) (w : HomogP ℓ) :
    liftAEnd ℓ j (liftBEnd ℓ j w) - liftBEnd ℓ j (liftAEnd ℓ j w) = axisRotEnd ℓ j w :=
  Subtype.ext (by
    rw [Submodule.coe_sub, liftAEnd, liftBEnd, axisRotEnd, restrictDeg_coe, restrictDeg_coe, restrictDeg_coe,
      restrictDeg_coe, restrictDeg_coe]
    exact bracket_liftA_liftB j _)

private lemma axisRotEnd_liftAEnd_comm (ℓ : ℕ) (j : Fin 3) (w : HomogP ℓ) :
    axisRotEnd ℓ j (liftAEnd ℓ j w) - liftAEnd ℓ j (axisRotEnd ℓ j w) = liftBEnd ℓ j w :=
  Subtype.ext (by
    rw [Submodule.coe_sub, liftAEnd, liftBEnd, axisRotEnd, restrictDeg_coe, restrictDeg_coe, restrictDeg_coe,
      restrictDeg_coe, restrictDeg_coe]
    exact bracket_axisRot_liftA j _)

private lemma axisRotEnd_liftBEnd_comm (ℓ : ℕ) (j : Fin 3) (w : HomogP ℓ) :
    axisRotEnd ℓ j (liftBEnd ℓ j w) - liftBEnd ℓ j (axisRotEnd ℓ j w) = - liftAEnd ℓ j w :=
  Subtype.ext (by
    rw [Submodule.coe_sub, Submodule.coe_neg, liftAEnd, liftBEnd, axisRotEnd, restrictDeg_coe, restrictDeg_coe,
      restrictDeg_coe, restrictDeg_coe, restrictDeg_coe]
    exact bracket_axisRot_liftB j _)

private lemma tripleE_tripleF_comm (ℓ : ℕ) (j : Fin 3) : ⁅tripleE ℓ j, tripleF ℓ j⁆ = tripleH ℓ j := by
  refine LinearMap.ext (fun w => ?_)
  change (tripleE ℓ j * tripleF ℓ j - tripleF ℓ j * tripleE ℓ j) w = tripleH ℓ j w
  have h1 := liftAEnd_liftBEnd_comm ℓ j w
  simp only [tripleE, tripleF, tripleH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, map_add, map_neg, map_smul]
  linear_combination (norm := module) (2 * Complex.I) • h1

private lemma tripleH_tripleE_comm (ℓ : ℕ) (j : Fin 3) : ⁅tripleH ℓ j, tripleE ℓ j⁆ = 2 • tripleE ℓ j := by
  refine LinearMap.ext (fun w => ?_)
  change (tripleH ℓ j * tripleE ℓ j - tripleE ℓ j * tripleH ℓ j) w = (2 • tripleE ℓ j) w
  have h1 := axisRotEnd_liftAEnd_comm ℓ j w
  have h2 := axisRotEnd_liftBEnd_comm ℓ j w
  simp only [tripleE, tripleH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, smul_smul]
  linear_combination (norm := module) (2 * Complex.I) • h1 + (-2 : ℂ) • h2 +
    Complex.I_mul_I • ((2 : ℂ) • (axisRotEnd ℓ j (liftBEnd ℓ j w) - liftBEnd ℓ j (axisRotEnd ℓ j w)))

private lemma tripleH_tripleF_comm (ℓ : ℕ) (j : Fin 3) : ⁅tripleH ℓ j, tripleF ℓ j⁆ = -(2 • tripleF ℓ j) := by
  refine LinearMap.ext (fun w => ?_)
  change (tripleH ℓ j * tripleF ℓ j - tripleF ℓ j * tripleH ℓ j) w = (-(2 • tripleF ℓ j)) w
  have h1 := axisRotEnd_liftAEnd_comm ℓ j w
  have h2 := axisRotEnd_liftBEnd_comm ℓ j w
  simp only [tripleF, tripleH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, map_add, map_neg, map_smul, smul_smul]
  linear_combination (norm := module) (-(2 * Complex.I)) • h1 + (-2 : ℂ) • h2 +
    Complex.I_mul_I • ((2 : ℂ) • (axisRotEnd ℓ j (liftBEnd ℓ j w) - liftBEnd ℓ j (axisRotEnd ℓ j w)))

private def highestVec (ℓ : ℕ) (j : Fin 3) : HomogP ℓ :=
  ⟨isotropicForm j ^ ℓ, (mem_homogeneousSubmodule _ _).mpr (by simpa using (isotropicForm_isHomogeneous j).pow ℓ)⟩

private lemma highestVec_ne_zero (ℓ : ℕ) (j : Fin 3) : highestVec ℓ j ≠ 0 := by
  intro h
  have h1 : isotropicForm j ^ ℓ = 0 := congrArg Subtype.val h
  exact pow_ne_zero ℓ (isotropicForm_ne_zero j) h1

private lemma axisRot_isotropicForm (j : Fin 3) : axisRot j (isotropicForm j) = C (-Complex.I) * isotropicForm j := by
  have hab := axisA_ne_axisB j
  simp only [axisRot, isotropicForm, map_add, Derivation.leibniz, rotDeriv_X, hab, hab.symm, if_true, if_false]
  simp only [derivation_C, smul_eq_mul, sub_zero, zero_sub, C_neg]
  linear_combination (X (axisB j) : CoeffP) * C_I_mul_C_I

private lemma liftA_isotropicForm (j : Fin 3) : liftA j (isotropicForm j) = X j := by
  have ha := axisA_ne j
  have hb := axisB_ne j
  have hab := axisA_ne_axisB j
  simp [liftA, isotropicForm, rotDeriv_X, ha, hb, hab.symm]

private lemma liftB_isotropicForm (j : Fin 3) : liftB j (isotropicForm j) = C Complex.I * X j := by
  have ha := axisA_ne j
  have hb := axisB_ne j
  have hab := axisA_ne_axisB j
  simp [liftB, isotropicForm, rotDeriv_X, ha, hb, hab]

private lemma tripleH_highestVec (ℓ : ℕ) (j : Fin 3) :
    tripleH ℓ j (highestVec ℓ j) = ((2 * ℓ : ℕ) : ℂ) • highestVec ℓ j := by
  refine Subtype.ext ?_
  rw [tripleH, LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_smul, axisRotEnd, restrictDeg_coe]
  change (2 * Complex.I) • axisRot j (isotropicForm j ^ ℓ) = ((2 * ℓ : ℕ) : ℂ) • isotropicForm j ^ ℓ
  rcases ℓ with _ | ℓ
  · simp
  · rw [Derivation.leibniz_pow, axisRot_isotropicForm, Nat.add_sub_cancel]
    simp only [smul_eq_C_mul, nsmul_eq_mul, smul_eq_mul, ← C_eq_coe_nat]
    have hs : (C (2 * Complex.I) : CoeffP) * C ((ℓ + 1 : ℕ) : ℂ) * C (-Complex.I) = C ((2 * (ℓ + 1) : ℕ) : ℂ) := by
      rw [← C_mul, ← C_mul]
      congr 1
      push_cast
      linear_combination (-2 * ((ℓ : ℂ) + 1)) * Complex.I_mul_I
    linear_combination (isotropicForm j ^ ℓ * isotropicForm j) * hs

private lemma tripleE_highestVec (ℓ : ℕ) (j : Fin 3) : tripleE ℓ j (highestVec ℓ j) = 0 := by
  refine Subtype.ext ?_
  rw [tripleE, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, liftAEnd, liftBEnd,
    restrictDeg_coe, restrictDeg_coe, Submodule.coe_zero]
  change liftA j (isotropicForm j ^ ℓ) + Complex.I • liftB j (isotropicForm j ^ ℓ) = 0
  rcases ℓ with _ | ℓ
  · simp
  · rw [Derivation.leibniz_pow, Derivation.leibniz_pow, liftA_isotropicForm, liftB_isotropicForm, Nat.add_sub_cancel]
    simp only [smul_eq_C_mul, nsmul_eq_mul, smul_eq_mul, ← C_eq_coe_nat]
    linear_combination (C ((ℓ + 1 : ℕ) : ℂ) * isotropicForm j ^ ℓ * X j : CoeffP) * C_I_mul_C_I

private lemma isSl2Triple_axis (ℓ : ℕ) (hℓ : ℓ ≠ 0) (j : Fin 3) :
    IsSl2Triple (tripleH ℓ j) (tripleE ℓ j) (tripleF ℓ j) where
  h_ne_zero := by
    intro h0
    have h1 := tripleH_highestVec ℓ j
    rw [h0, LinearMap.zero_apply] at h1
    have h2 : ((2 * ℓ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * ℓ ≠ 0)
    exact highestVec_ne_zero ℓ j ((smul_eq_zero.mp h1.symm).resolve_left h2)
  lie_e_f := tripleE_tripleF_comm ℓ j
  lie_h_e_nsmul := tripleH_tripleE_comm ℓ j
  lie_h_f_nsmul := tripleH_tripleF_comm ℓ j

private lemma hasPrimitiveVector_axis (ℓ : ℕ) (hℓ : ℓ ≠ 0) (j : Fin 3) :
    (isSl2Triple_axis ℓ hℓ j).HasPrimitiveVectorWith (highestVec ℓ j) ((2 * ℓ : ℕ) : ℂ) where
  ne_zero := highestVec_ne_zero ℓ j
  lie_h := by rw [Module.End.lie_apply, tripleH_highestVec]
  lie_e := by rw [Module.End.lie_apply, tripleE_highestVec]

section string
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private def stringVec (f : Module.End ℂ M) (z : M) (n : ℕ) (i : Fin (n + 1)) : M := (f ^ (i : ℕ)) z

private def stringMap (f : Module.End ℂ M) (z : M) (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] M :=
  ∑ i : Fin (n + 1), (LinearMap.proj i : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ).smulRight (stringVec f z n i)

private lemma stringMap_apply (f : Module.End ℂ M) (z : M) (n : ℕ) (a : Fin (n + 1) → ℂ) :
    stringMap f z n a = ∑ i : Fin (n + 1), a i • stringVec f z n i := by
  simp [stringMap, LinearMap.sum_apply]

private def coordH (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) :=
  LinearMap.pi (fun i : Fin (n + 1) =>
    ((n : ℂ) - 2 * ((i : ℕ) : ℂ)) • (LinearMap.proj i : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ))

private def coordF (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) :=
  LinearMap.pi (fun i : Fin (n + 1) =>
    Fin.cases (0 : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ) (fun i' : Fin n => LinearMap.proj (Fin.castSucc i')) i)

private def coordE (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) :=
  LinearMap.pi (fun i : Fin (n + 1) =>
    Fin.lastCases (0 : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ)
      (fun i' : Fin n => ((((i' : ℕ) : ℂ) + 1) * ((n : ℂ) - ((i' : ℕ) : ℂ))) •
        (LinearMap.proj (Fin.succ i') : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ)) i)

private lemma coordH_apply (n : ℕ) (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    coordH n a i = ((n : ℂ) - 2 * ((i : ℕ) : ℂ)) * a i := by
  simp [coordH, LinearMap.pi_apply]

private lemma coordF_apply_zero (n : ℕ) (a : Fin (n + 1) → ℂ) : coordF n a 0 = 0 := by
  simp [coordF, LinearMap.pi_apply]

private lemma coordF_apply_succ (n : ℕ) (a : Fin (n + 1) → ℂ) (i : Fin n) :
    coordF n a (Fin.succ i) = a (Fin.castSucc i) := by
  simp [coordF, LinearMap.pi_apply]

private lemma coordE_apply_last (n : ℕ) (a : Fin (n + 1) → ℂ) : coordE n a (Fin.last n) = 0 := by
  simp [coordE, LinearMap.pi_apply]

private lemma coordE_apply_castSucc (n : ℕ) (a : Fin (n + 1) → ℂ) (i : Fin n) :
    coordE n a (Fin.castSucc i) = ((((i : ℕ) : ℂ) + 1) * ((n : ℂ) - ((i : ℕ) : ℂ))) * a (Fin.succ i) := by
  simp [coordE, LinearMap.pi_apply]

variable {h e f : Module.End ℂ M} {t : IsSl2Triple h e f} {z : M} {n : ℕ}

private lemma toEnd_end_eq (x : Module.End ℂ M) : LieModule.toEnd ℂ (Module.End ℂ M) M x = x :=
  LinearMap.ext (fun m => by rw [LieModule.toEnd_apply_apply, Module.End.lie_apply])

private lemma h_stringVec (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) (i : Fin (n + 1)) :
    h (stringVec f z n i) = ((n : ℂ) - 2 * ((i : ℕ) : ℂ)) • stringVec f z n i := by
  have := hz.lie_h_pow_toEnd_f (i : ℕ)
  rwa [toEnd_end_eq, Module.End.lie_apply] at this

private lemma f_stringVec (f' : Module.End ℂ M) (z' : M) (n' : ℕ) (i : Fin (n' + 1)) :
    f' (stringVec f' z' n' i) = (f' ^ ((i : ℕ) + 1)) z' := by
  rw [stringVec, pow_succ', Module.End.mul_apply]

private lemma e_stringVec_succ (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) (i : Fin n) :
    e (stringVec f z n (Fin.succ i)) =
      ((((i : ℕ) : ℂ) + 1) * ((n : ℂ) - ((i : ℕ) : ℂ))) • stringVec f z n (Fin.castSucc i) := by
  have := hz.lie_e_pow_succ_toEnd_f (i : ℕ)
  rw [toEnd_end_eq, Module.End.lie_apply] at this
  simpa [stringVec, Fin.val_succ, Fin.val_castSucc] using this

private lemma e_stringVec_zero (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) : e (stringVec f z n 0) = 0 := by
  have := hz.lie_e
  rw [Module.End.lie_apply] at this
  simpa [stringVec] using this

private lemma stringMap_coordH (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) (a : Fin (n + 1) → ℂ) :
    stringMap f z n (coordH n a) = h (stringMap f z n a) := by
  rw [stringMap_apply, stringMap_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, h_stringVec hz, coordH_apply, mul_smul, smul_comm]

private lemma stringMap_coordF (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) [IsNoetherian ℂ M]
    (a : Fin (n + 1) → ℂ) : stringMap f z n (coordF n a) = f (stringMap f z n a) := by
  rw [stringMap_apply, stringMap_apply, map_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc, coordF_apply_zero,
    zero_smul, zero_add]
  have hlast : f (stringVec f z n (Fin.last n)) = 0 := by
    have h0 := hz.pow_toEnd_f_eq_zero_of_eq_nat rfl
    rw [toEnd_end_eq] at h0
    rw [f_stringVec, Fin.val_last]
    exact h0
  rw [map_smul, hlast, smul_zero, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coordF_apply_succ, map_smul, f_stringVec, stringVec, Fin.val_castSucc, Fin.val_succ]

private lemma stringMap_coordE (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) (a : Fin (n + 1) → ℂ) :
    stringMap f z n (coordE n a) = e (stringMap f z n a) := by
  rw [stringMap_apply, stringMap_apply, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_succ, coordE_apply_last,
    zero_smul, add_zero, map_smul, e_stringVec_zero hz, smul_zero, zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coordE_apply_castSucc, map_smul, e_stringVec_succ hz, mul_smul, smul_comm]

private lemma stringMap_injective (hz : t.HasPrimitiveVectorWith z ((n : ℕ) : ℂ)) :
    Function.Injective (stringMap f z n) := by
  have hli : LinearIndependent ℂ (stringVec f z n) := by
    refine h.eigenvectors_linearIndependent' (fun i : Fin (n + 1) => (n : ℂ) - 2 * ((i : ℕ) : ℂ)) ?_ _ (fun i => ?_)
    · intro i₁ i₂ h12
      have : ((i₁ : ℕ) : ℂ) = ((i₂ : ℕ) : ℂ) := by linear_combination (-1 / 2 : ℂ) * h12
      exact Fin.ext (by exact_mod_cast this)
    · rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      refine ⟨h_stringVec hz i, ?_⟩
      have hne := hz.pow_toEnd_f_ne_zero_of_eq_nat rfl (Nat.lt_succ_iff.mp i.isLt)
      rwa [toEnd_end_eq] at hne
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  rw [stringMap_apply] at ha
  funext i
  exact linearIndependent_iff'.mp hli Finset.univ a ha i (Finset.mem_univ i)

private lemma range_stable (Φ₁ : (Fin (n + 1) → ℂ) →ₗ[ℂ] M) (op₁ : Module.End ℂ M)
    (ophat : Module.End ℂ (Fin (n + 1) → ℂ)) (h₁ : ∀ a, Φ₁ (ophat a) = op₁ (Φ₁ a)) :
    ∀ w ∈ LinearMap.range Φ₁, op₁ w ∈ LinearMap.range Φ₁ := by
  rintro _ ⟨a, rfl⟩
  exact ⟨ophat a, h₁ a⟩

private lemma transfer_intertwines {M₂ : Type*} [AddCommGroup M₂] [Module ℂ M₂]
    (Φ₁ : (Fin (n + 1) → ℂ) →ₗ[ℂ] M) (Φ₂ : (Fin (n + 1) → ℂ) →ₗ[ℂ] M₂) (hΦ₁ : Function.Injective Φ₁)
    (op₁ : Module.End ℂ M) (op₂ : Module.End ℂ M₂) (ophat : Module.End ℂ (Fin (n + 1) → ℂ))
    (h₁ : ∀ a, Φ₁ (ophat a) = op₁ (Φ₁ a)) (h₂ : ∀ a, Φ₂ (ophat a) = op₂ (Φ₂ a)) (a : Fin (n + 1) → ℂ) :
    Φ₂ ((LinearEquiv.ofInjective Φ₁ hΦ₁).symm ⟨op₁ (Φ₁ a), range_stable Φ₁ op₁ ophat h₁ _ ⟨a, rfl⟩⟩) =
      op₂ (Φ₂ ((LinearEquiv.ofInjective Φ₁ hΦ₁).symm ⟨Φ₁ a, ⟨a, rfl⟩⟩)) := by
  have hA : (LinearEquiv.ofInjective Φ₁ hΦ₁).symm ⟨Φ₁ a, ⟨a, rfl⟩⟩ = a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hB : (LinearEquiv.ofInjective Φ₁ hΦ₁).symm ⟨op₁ (Φ₁ a), range_stable Φ₁ op₁ ophat h₁ _ ⟨a, rfl⟩⟩ = ophat a := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact (h₁ a).symm)
  rw [hA, hB, h₂]

end string

private def applyCoeff (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) : CoeffP :=
  ∑ m ∈ W.support, monomial m (Λ (coeff m W))

private lemma coeff_applyCoeff (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) (m : Fin 3 →₀ ℕ) :
    coeff m (applyCoeff Λ W) = Λ (coeff m W) := by
  simp only [applyCoeff, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with hm
  · rw [hm, map_zero]
  · rfl

private lemma applyCoeff_isHomogeneous (Λ : CoeffP →ₗ[ℂ] ℂ) {W : OuterP} {ℓ : ℕ} (hW : W.IsHomogeneous ℓ) :
    (applyCoeff Λ W).IsHomogeneous ℓ := by
  refine IsHomogeneous.sum _ _ _ (fun m hm => isHomogeneous_monomial _ ?_)
  by_contra hne
  exact (mem_support_iff.mp hm) (hW.coeff_eq_zero hne)

private lemma applyCoeff_ext {Λ : CoeffP →ₗ[ℂ] ℂ} {W : OuterP} {p : CoeffP}
    (hp : ∀ m, coeff m p = Λ (coeff m W)) : p = applyCoeff Λ W :=
  MvPolynomial.ext _ _ (fun m => by rw [hp, coeff_applyCoeff])

private lemma coeff_pderiv_eq {R : Type} [CommRing R] (i : Fin 3) (p : MvPolynomial (Fin 3) R) (m : Fin 3 →₀ ℕ) :
    coeff m (pderiv i p) = (m i + 1) • coeff (m + Finsupp.single i 1) p := by
  refine induction_on' p (fun d r => ?_) (fun p q hp hq => ?_)
  · rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hd : d = m + Finsupp.single i 1
    · subst hd
      simp [nsmul_eq_mul, mul_comm]
    · rw [if_neg hd, smul_zero]
      by_cases h0 : d i = 0
      · simp [h0]
      · rw [if_neg]
        intro hdm
        apply hd
        rw [← hdm, tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
  · rw [map_add, coeff_add, coeff_add, hp, hq, smul_add]

private lemma pderiv_applyCoeff (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) (i : Fin 3) :
    pderiv i (applyCoeff Λ W) = applyCoeff Λ (pderiv i W) := by
  refine applyCoeff_ext (fun m => ?_)
  rw [coeff_pderiv_eq, coeff_pderiv_eq, coeff_applyCoeff, map_nsmul]

private lemma eval_applyCoeff (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) (y : Fin 3 → ℂ) :
    eval y (applyCoeff Λ W) = Λ (aeval (fun i => (C (y i) : CoeffP)) W) := by
  conv_rhs => rw [W.as_sum, map_sum, map_sum]
  rw [applyCoeff, eval_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [eval_monomial, aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
  have hprod : (m.prod fun n e => (C (y n) : CoeffP) ^ e) = C (m.prod fun n e => y n ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [hprod, mul_comm (coeff m W), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]

private lemma eval_column_realisation (j : Fin 3) (p : CoeffP) (y : Fin 3 × Fin 3 → ℂ) :
    eval y (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) = eval (fun a => y (a, j)) p := by
  have hcomp : (eval y).comp (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) :
      CoeffP →ₐ[ℂ] MvPolynomial (Fin 3 × Fin 3) ℂ).toRingHom = eval (fun a => y (a, j)) := by
    refine ringHom_ext (fun r => ?_) (fun a => ?_) <;> simp
  exact RingHom.congr_fun hcomp p

private lemma applyCoeff_zero (Λ : CoeffP →ₗ[ℂ] ℂ) : applyCoeff Λ 0 = 0 := by
  simp [applyCoeff]

private lemma lapL_applyCoeff (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) : lapL (applyCoeff Λ W) = applyCoeff Λ (lapL W) := by
  refine applyCoeff_ext (fun m => ?_)
  simp only [lapL_apply, coeff_sum, pderiv_applyCoeff, coeff_applyCoeff, map_sum]

private lemma pairT_isHomogeneous : (pairT : OuterP).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => by simpa using (isHomogeneous_C _ (X i : CoeffP)).mul (isHomogeneous_X _ i))

private lemma innerS_isHomogeneous : (innerS : OuterP).IsHomogeneous 0 :=
  IsHomogeneous.sum _ _ _ (fun i _ => by simpa using (isHomogeneous_C _ (X i : CoeffP)).pow 2)

private lemma outerU_isHomogeneous : (outerU : OuterP).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ (fun i _ => by simpa using (isHomogeneous_X _ i).pow 2)

private lemma pairG_isHomogeneous : (pairG : OuterP).IsHomogeneous 2 := by
  have h1 := innerS_isHomogeneous.mul outerU_isHomogeneous
  rw [zero_add] at h1
  exact h1.sub (by simpa using pairT_isHomogeneous.pow 2)

private lemma pairSubst_sum_isHomogeneous {ι : Type} (s : Finset ι) (c : ι → ℂ) (m n : ι → ℕ) {ℓ : ℕ}
    (hmn : ∀ e ∈ s, m e + 2 * n e = ℓ) :
    (pairSubst (∑ e ∈ s, C (c e) * X 0 ^ m e * X 1 ^ n e)).IsHomogeneous ℓ := by
  rw [map_sum]
  refine IsHomogeneous.sum _ _ _ (fun e he => ?_)
  simp only [pairSubst, map_mul, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hmn e he, MvPolynomial.algebraMap_apply]
  have h := ((isHomogeneous_C _ (algebraMap ℂ CoeffP (c e))).mul (pairT_isHomogeneous.pow (m e))).mul
    (pairG_isHomogeneous.pow (n e))
  simpa using h

private lemma lapL_pairSubst_eq_zero (j : Fin 3) (Ψ : MvPolynomial (Fin 2) ℂ) (h : lapL (axisSubst j Ψ) = 0) :
    lapL (pairSubst Ψ) = 0 := by
  rw [lapL_axisSubst] at h
  have h0 : radialOp Ψ = 0 := axisSubst_injective j (by rw [h, map_zero])
  rw [lapL_pairSubst, h0, map_zero, mul_zero]

private lemma row_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk1 : k * k.transpose = 1) (l m : Fin 3) :
    (C ((k l 0 : ℝ) : ℂ) * C ((k m 0 : ℝ) : ℂ) + C ((k l 1 : ℝ) : ℂ) * C ((k m 1 : ℝ) : ℂ) +
      C ((k l 2 : ℝ) : ℂ) * C ((k m 2 : ℝ) : ℂ) : CoeffP) = if l = m then 1 else 0 := by
  have h := congrFun (congrFun hk1 l) m
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h
  simp only [Matrix.transpose_apply] at h
  rw [← C_mul, ← C_mul, ← C_mul, ← C_add, ← C_add, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, ← Complex.ofReal_add, h]
  split_ifs <;> simp

private lemma col_unit {k : Matrix (Fin 3) (Fin 3) ℝ} (hk2 : k.transpose * k = 1) (j : Fin 3) :
    (C ((k 0 j : ℝ) : ℂ) * C ((k 0 j : ℝ) : ℂ) + C ((k 1 j : ℝ) : ℂ) * C ((k 1 j : ℝ) : ℂ) +
      C ((k 2 j : ℝ) : ℂ) * C ((k 2 j : ℝ) : ℂ) : CoeffP) = 1 := by
  have h := congrFun (congrFun hk2 j) j
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h
  simp only [Matrix.transpose_apply] at h
  rw [← C_mul, ← C_mul, ← C_mul, ← C_add, ← C_add, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, ← Complex.ofReal_add, h]
  simp

private def columnEval (k : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : OuterP →ₐ[CoeffP] CoeffP :=
  aeval (fun i => (C ((k i j : ℝ) : ℂ) : CoeffP))

private lemma columnEval_pairT (k : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    columnEval k j pairT = matrixSubst k (X j) := by
  simp only [columnEval, pairT, map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X,
    matrixSubst_X]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma columnEval_pairG (k : Matrix (Fin 3) (Fin 3) ℝ) (hk1 : k * k.transpose = 1) (hk2 : k.transpose * k = 1)
    (j : Fin 3) : columnEval k j pairG = matrixSubst k (planeRadiusSq j) := by
  have e00 := row_orth hk1 0 0
  have e11 := row_orth hk1 1 1
  have e22 := row_orth hk1 2 2
  have e01 := row_orth hk1 0 1
  have e02 := row_orth hk1 0 2
  have e12 := row_orth hk1 1 2
  have f := col_unit hk2 j
  simp only [if_true] at e00 e11 e22
  simp only [Fin.zero_ne_one, Fin.reduceEq, if_false] at e01 e02 e12
  simp only [columnEval, pairG, innerS, outerU, pairT, map_sub, map_mul, map_pow, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, aeval_X, planeRadiusSq, map_add, matrixSubst_X, Fin.sum_univ_three]
  fin_cases j <;> simp only [axisA, axisB, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at f ⊢ <;>
  linear_combination (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 : CoeffP) * f - (X 0 ^ 2 : CoeffP) * e00 - (X 1 ^ 2 : CoeffP) * e11 -
    (X 2 ^ 2 : CoeffP) * e22 - (2 * X 0 * X 1 : CoeffP) * e01 - (2 * X 0 * X 2 : CoeffP) * e02 -
    (2 * X 1 * X 2 : CoeffP) * e12

private lemma matrixSubst_axisSubst (k : Matrix (Fin 3) (Fin 3) ℝ) (hk1 : k * k.transpose = 1)
    (hk2 : k.transpose * k = 1) (j : Fin 3) (Ψ : MvPolynomial (Fin 2) ℂ) :
    matrixSubst k (axisSubst j Ψ) = columnEval k j (pairSubst Ψ) := by
  rw [← AlgHom.restrictScalars_apply ℂ (columnEval k j), axisSubst, pairSubst, ← AlgHom.comp_apply, comp_aeval,
    ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i
  · show matrixSubst k (X j) = columnEval k j pairT
    exact (columnEval_pairT k j).symm
  · show matrixSubst k (planeRadiusSq j) = columnEval k j pairG
    exact (columnEval_pairG k hk1 hk2 j).symm

private lemma eval_applyCoeff_column (Λ : CoeffP →ₗ[ℂ] ℂ) (W : OuterP) (k : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    eval (fun i => ((k i j : ℝ) : ℂ)) (applyCoeff Λ W) = Λ (columnEval k j W) :=
  eval_applyCoeff Λ W _

end AxisHarmonics
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private noncomputable def planeRotation (c₁ c₂ : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i k =>
  if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
  if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
  if i = k then (1 : ℝ) else 0

private theorem planeRotation_zero_one_mem (s : ℝ) :
    planeRotation 0 1 s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.cos_sq_add_sin_sq s]

private theorem planeRotation_zero_two_mem (s : ℝ) :
    planeRotation 0 2 s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.cos_sq_add_sin_sq s]

private theorem planeRotation_one_two_mem (s : ℝ) :
    planeRotation 1 2 s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.cos_sq_add_sin_sq s]

private theorem planeRotation_zero_one_add (s t : ℝ) :
    planeRotation 0 1 (s + t) = planeRotation 0 1 s * planeRotation 0 1 t := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring1

private theorem planeRotation_zero_two_add (s t : ℝ) :
    planeRotation 0 2 (s + t) = planeRotation 0 2 s * planeRotation 0 2 t := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring1

private theorem planeRotation_one_two_add (s t : ℝ) :
    planeRotation 1 2 (s + t) = planeRotation 1 2 s * planeRotation 1 2 t := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring1

private theorem planeRotation_zero_one_zero : planeRotation 0 1 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_zero_two_zero : planeRotation 0 2 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_one_two_zero : planeRotation 1 2 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_zero_one_two_pi : planeRotation 0 1 (2 * Real.pi) = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_zero_two_two_pi : planeRotation 0 2 (2 * Real.pi) = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_one_two_two_pi : planeRotation 1 2 (2 * Real.pi) = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation]

private theorem planeRotation_zero_one_det (s : ℝ) : (planeRotation 0 1 s).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [planeRotation]
  nlinarith [Real.cos_sq_add_sin_sq s]

private theorem planeRotation_zero_two_det (s : ℝ) : (planeRotation 0 2 s).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [planeRotation]
  nlinarith [Real.cos_sq_add_sin_sq s]

private theorem planeRotation_one_two_det (s : ℝ) : (planeRotation 1 2 s).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [planeRotation]
  nlinarith [Real.cos_sq_add_sin_sq s]

private theorem orthogonal_mul_mem {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hB : B ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : A * B ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff] at hA hB ⊢
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB, Matrix.one_mul, hA]

private theorem neg_one_mem_orthogonal : (-1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, mul_one]

private theorem det_neg_one_fin_three : (-1 : Matrix (Fin 3) (Fin 3) ℝ).det = -1 := by
  rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
  norm_num

private theorem orthogonal_neg_mem {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    -A ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff] at hA ⊢
  rw [Matrix.transpose_neg, neg_mul_neg, hA]

private theorem orthogonal_det_eq_one_or_neg_one {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : A.det = 1 ∨ A.det = -1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at hA
  have h := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.mp h

private theorem det_neg_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) : (-A).det = -A.det := by
  rw [Matrix.det_neg, Fintype.card_fin]
  norm_num

private theorem exists_planeRotations_column (u : Fin 3 → ℝ) (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1) :
    ∃ α β : ℝ, ∀ i, (planeRotation 0 1 α * planeRotation 1 2 β) i 2 = u i := by
  set w : ℂ := ⟨-u 1, u 0⟩ with hw
  have hwre : w.re = -u 1 := rfl
  have hwim : w.im = u 0 := rfl
  have hwsq : ‖w‖ * ‖w‖ = u 0 * u 0 + u 1 * u 1 := by
    rw [Complex.norm_mul_self_eq_normSq, hw, Complex.normSq_mk]
    ring1
  have hcosα : ‖w‖ * Real.cos (Complex.arg w) = -u 1 := by
    have h := congrArg Complex.re (Complex.norm_mul_cos_add_sin_mul_I w)
    rw [hwre] at h
    simpa using h
  have hsinα : ‖w‖ * Real.sin (Complex.arg w) = u 0 := by
    have h := congrArg Complex.im (Complex.norm_mul_cos_add_sin_mul_I w)
    rw [hwim] at h
    simpa using h
  set w' : ℂ := ⟨u 2, ‖w‖⟩ with hw'
  have hw're : w'.re = u 2 := rfl
  have hw'im : w'.im = ‖w‖ := rfl
  have hw'norm : ‖w'‖ = 1 := by
    have h2 : ‖w'‖ * ‖w'‖ = 1 := by
      rw [Complex.norm_mul_self_eq_normSq, hw', Complex.normSq_mk]
      linear_combination hu + hwsq
    nlinarith [norm_nonneg w', h2]
  have hcosβ : Real.cos (Complex.arg w') = u 2 := by
    have h := congrArg Complex.re (Complex.norm_mul_cos_add_sin_mul_I w')
    rw [hw're, hw'norm] at h
    simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using h
  have hsinβ : Real.sin (Complex.arg w') = ‖w‖ := by
    have h := congrArg Complex.im (Complex.norm_mul_cos_add_sin_mul_I w')
    rw [hw'im, hw'norm] at h
    simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using h
  refine ⟨Complex.arg w, Complex.arg w', fun i => ?_⟩
  fin_cases i
  · simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, hsinβ]
    linear_combination hsinα
  · simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, hsinβ]
    linear_combination -hcosα
  · simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_three, hcosβ]

private theorem eq_planeRotation_of_column (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hdet : m.det = 1) (h02 : m 0 2 = 0) (h12 : m 1 2 = 0) (h22 : m 2 2 = 1) : ∃ γ : ℝ, m = planeRotation 0 1 γ := by
  rw [Matrix.mem_orthogonalGroup_iff] at hm
  have hrow0 : m 0 0 * m 0 0 + m 0 1 * m 0 1 = 1 := by
    have h := congrFun (congrFun hm 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02] at h
    linear_combination h
  have hrow01 : m 0 0 * m 1 0 + m 0 1 * m 1 1 = 0 := by
    have h := congrFun (congrFun hm 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12] at h
    linear_combination h
  have hrow2 : m 2 0 * m 2 0 + m 2 1 * m 2 1 = 0 := by
    have h := congrFun (congrFun hm 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h22] at h
    linear_combination h
  have h20 : m 2 0 = 0 := by nlinarith [mul_self_nonneg (m 2 0), mul_self_nonneg (m 2 1)]
  have h21 : m 2 1 = 0 := by nlinarith [mul_self_nonneg (m 2 0), mul_self_nonneg (m 2 1)]
  have hdet' : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    rw [h02, h12, h22, h20, h21] at hdet
    linear_combination hdet
  have h11 : m 1 1 = m 0 0 := by
    linear_combination (-(m 1 1)) * hrow0 + m 0 0 * hdet' + m 0 1 * hrow01
  have h10 : m 1 0 = - m 0 1 := by
    linear_combination (-(m 1 0)) * hrow0 - m 0 1 * hdet' + m 0 0 * hrow01
  set z : ℂ := ⟨m 0 0, m 1 0⟩ with hz
  have hzre : z.re = m 0 0 := rfl
  have hzim : z.im = m 1 0 := rfl
  have hznorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ * ‖z‖ = 1 := by
      rw [Complex.norm_mul_self_eq_normSq, hz, Complex.normSq_mk, h10]
      linear_combination hrow0
    nlinarith [norm_nonneg z, h2]
  have hcos : Real.cos (Complex.arg z) = m 0 0 := by
    have h := congrArg Complex.re (Complex.norm_mul_cos_add_sin_mul_I z)
    rw [hzre, hznorm] at h
    simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using h
  have hsin : Real.sin (Complex.arg z) = m 1 0 := by
    have h := congrArg Complex.im (Complex.norm_mul_cos_add_sin_mul_I z)
    rw [hzim, hznorm] at h
    simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using h
  refine ⟨Complex.arg z, ?_⟩
  ext i k
  fin_cases i <;> fin_cases k <;> simp [planeRotation, hcos, hsin, h02, h12, h22, h20, h21, h11, h10]

private theorem orthogonal_induction (P : Matrix (Fin 3) (Fin 3) ℝ → Prop) (h01 : ∀ s, P (planeRotation 0 1 s))
    (h12 : ∀ s, P (planeRotation 1 2 s)) (hneg : P (-1))
    (hmul : ∀ x y, x ∈ Matrix.orthogonalGroup (Fin 3) ℝ → y ∈ Matrix.orthogonalGroup (Fin 3) ℝ → P x → P y → P (x * y))
    (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : P k := by
  have hrot : ∀ g ∈ Matrix.orthogonalGroup (Fin 3) ℝ, g.det = 1 → P g := by
    intro g hg hdet
    have hcol : g 0 2 * g 0 2 + g 1 2 * g 1 2 + g 2 2 * g 2 2 = 1 := by
      have hg' := hg
      rw [Matrix.mem_orthogonalGroup_iff'] at hg'
      have h := congrFun (congrFun hg' 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using h
    obtain ⟨α, β, hαβ⟩ := exists_planeRotations_column (fun i => g i 2) hcol
    set a := planeRotation 0 1 α with ha
    set b := planeRotation 1 2 β with hb
    set a' := planeRotation 0 1 (-α) with ha'
    set b' := planeRotation 1 2 (-β) with hb'
    have haa' : a * a' = 1 := by
      rw [ha, ha', ← planeRotation_zero_one_add, add_neg_cancel, planeRotation_zero_one_zero]
    have ha'a : a' * a = 1 := by
      rw [ha, ha', ← planeRotation_zero_one_add, neg_add_cancel, planeRotation_zero_one_zero]
    have hbb' : b * b' = 1 := by
      rw [hb, hb', ← planeRotation_one_two_add, add_neg_cancel, planeRotation_one_two_zero]
    have hb'b : b' * b = 1 := by
      rw [hb, hb', ← planeRotation_one_two_add, neg_add_cancel, planeRotation_one_two_zero]
    set m := b' * a' * g with hm
    have hm_mem : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
      orthogonal_mul_mem (orthogonal_mul_mem (planeRotation_one_two_mem _) (planeRotation_zero_one_mem _)) hg
    have hm_det : m.det = 1 := by
      rw [hm, Matrix.det_mul, Matrix.det_mul, hb', ha', planeRotation_one_two_det, planeRotation_zero_one_det, hdet]
      ring1
    have hm_col : ∀ i, m i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := by
      intro i
      have h1 : m i 2 = (b' * a' * (a * b)) i 2 := by
        rw [hm, Matrix.mul_apply (M := b' * a') (N := g), Matrix.mul_apply (M := b' * a') (N := a * b)]
        exact Finset.sum_congr rfl fun l _ => by rw [hαβ l]
      rw [h1, Matrix.mul_assoc, ← Matrix.mul_assoc a', ha'a, Matrix.one_mul, hb'b]
    obtain ⟨γ, hγ⟩ := eq_planeRotation_of_column m hm_mem hm_det (by simpa using hm_col 0) (by simpa using hm_col 1)
      (by simpa using hm_col 2)
    have hg_eq : g = a * (b * m) := by
      rw [hm]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc b b', hbb', Matrix.one_mul, ← Matrix.mul_assoc a a', haa', Matrix.one_mul]
    rw [hg_eq, hγ]
    exact hmul _ _ (planeRotation_zero_one_mem α) (orthogonal_mul_mem (planeRotation_one_two_mem β)
      (planeRotation_zero_one_mem γ)) (h01 α) (hmul _ _ (planeRotation_one_two_mem β) (planeRotation_zero_one_mem γ)
      (h12 β) (h01 γ))
  rcases orthogonal_det_eq_one_or_neg_one hk with hdet | hdet
  · exact hrot k hk hdet
  · have hnk : (-k).det = 1 := by rw [det_neg_fin_three, hdet, neg_neg]
    have hkeq : (-1 : Matrix (Fin 3) (Fin 3) ℝ) * (-k) = k := (neg_one_mul (-k)).trans (neg_neg k)
    have hP : P ((-1 : Matrix (Fin 3) (Fin 3) ℝ) * (-k)) :=
      hmul _ _ neg_one_mem_orthogonal (orthogonal_neg_mem hk) hneg (hrot (-k) (orthogonal_neg_mem hk) hnk)
    rwa [hkeq] at hP

private theorem eval_aeval_eq (f : Fin 3 → MvPolynomial (Fin 3) ℂ) (y : Fin 3 → ℂ) (q : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval y (MvPolynomial.aeval f q) = MvPolynomial.eval (fun i => MvPolynomial.eval y (f i)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p₁ p₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | mul_X p i h => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, h]

private theorem eval_matrixSubst (k : Matrix (Fin 3) (Fin 3) ℝ) (y : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval y (AxisHarmonics.matrixSubst k p) =
      MvPolynomial.eval (fun i : Fin 3 => ∑ l : Fin 3, ((k l i : ℝ) : ℂ) * y l) p := by
  rw [AxisHarmonics.matrixSubst, eval_aeval_eq]
  have h : (fun i : Fin 3 => MvPolynomial.eval y
      (∑ l : Fin 3, MvPolynomial.C ((k l i : ℝ) : ℂ) * (MvPolynomial.X l : MvPolynomial (Fin 3) ℂ))) =
      fun i : Fin 3 => ∑ l : Fin 3, ((k l i : ℝ) : ℂ) * y l := by
    funext i
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [h]

private theorem hasDerivAt_eval_matrixSubst_planeRotation01 (q : MvPolynomial (Fin 3) ℂ) (y : Fin 3 → ℂ) (s₀ : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 1 s) q))
      (MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 1 s₀) (AxisHarmonics.rotDeriv 0 1 q))) s₀ := by
  let v : ℝ → Fin 3 → ℂ := fun s i => ∑ l : Fin 3, ((planeRotation 0 1 s l i : ℝ) : ℂ) * y l
  have hR : ∀ (s : ℝ) (p : MvPolynomial (Fin 3) ℂ),
      MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 1 s) p) = MvPolynomial.eval (v s) p :=
    fun s p => eval_matrixSubst _ _ _
  have hv0 : ∀ s, v s 0 = ((Real.cos s : ℝ) : ℂ) * y 0 + ((Real.sin s : ℝ) : ℂ) * y 1 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv1 : ∀ s, v s 1 = -((Real.sin s : ℝ) : ℂ) * y 0 + ((Real.cos s : ℝ) : ℂ) * y 1 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv2 : ∀ s, v s 2 = y 2 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hderiv : ∀ i, HasDerivAt (fun s => v s i) (![v s₀ 1, -v s₀ 0, 0] i) s₀ := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have h : HasDerivAt (fun s => ((Real.cos s : ℝ) : ℂ) * y 0 + ((Real.sin s : ℝ) : ℂ) * y 1)
          (((-Real.sin s₀ : ℝ) : ℂ) * y 0 + ((Real.cos s₀ : ℝ) : ℂ) * y 1) s₀ :=
        ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 0)).add
          ((Real.hasDerivAt_sin s₀).ofReal_comp.mul_const (y 1))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv0 s)).congr_deriv ?_
      rw [hv1 s₀]
      push_cast
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h1 : HasDerivAt (fun s : ℝ => -((Real.sin s : ℝ) : ℂ)) (-((Real.cos s₀ : ℝ) : ℂ)) s₀ :=
        (Real.hasDerivAt_sin s₀).ofReal_comp.neg
      have h : HasDerivAt (fun s => -((Real.sin s : ℝ) : ℂ) * y 0 + ((Real.cos s : ℝ) : ℂ) * y 1)
          (-((Real.cos s₀ : ℝ) : ℂ) * y 0 + ((-Real.sin s₀ : ℝ) : ℂ) * y 1) s₀ :=
        (h1.mul_const (y 0)).add ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 1))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv1 s)).congr_deriv ?_
      rw [hv0 s₀]
      push_cast
      ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact (hasDerivAt_const s₀ (y 2)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv2 s)
  have hfun : (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 1 s) q)) =
      fun s => MvPolynomial.eval (v s) q := by
    funext s
    exact hR s q
  rw [hfun, hR]
  refine (hasDerivAt_eval_of_hasDerivAt q v _ s₀ hderiv).congr_deriv ?_
  rw [AxisHarmonics.rotDeriv_apply]
  simp only [map_sub, map_mul, MvPolynomial.eval_X, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, add_zero]
  ring

private theorem hasDerivAt_eval_matrixSubst_planeRotation02 (q : MvPolynomial (Fin 3) ℂ) (y : Fin 3 → ℂ) (s₀ : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 2 s) q))
      (MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 2 s₀) (AxisHarmonics.rotDeriv 0 2 q))) s₀ := by
  let v : ℝ → Fin 3 → ℂ := fun s i => ∑ l : Fin 3, ((planeRotation 0 2 s l i : ℝ) : ℂ) * y l
  have hR : ∀ (s : ℝ) (p : MvPolynomial (Fin 3) ℂ),
      MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 2 s) p) = MvPolynomial.eval (v s) p :=
    fun s p => eval_matrixSubst _ _ _
  have hv0 : ∀ s, v s 0 = ((Real.cos s : ℝ) : ℂ) * y 0 + ((Real.sin s : ℝ) : ℂ) * y 2 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv2 : ∀ s, v s 2 = -((Real.sin s : ℝ) : ℂ) * y 0 + ((Real.cos s : ℝ) : ℂ) * y 2 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv1 : ∀ s, v s 1 = y 1 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hderiv : ∀ i, HasDerivAt (fun s => v s i) (![v s₀ 2, 0, -v s₀ 0] i) s₀ := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have h : HasDerivAt (fun s => ((Real.cos s : ℝ) : ℂ) * y 0 + ((Real.sin s : ℝ) : ℂ) * y 2)
          (((-Real.sin s₀ : ℝ) : ℂ) * y 0 + ((Real.cos s₀ : ℝ) : ℂ) * y 2) s₀ :=
        ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 0)).add
          ((Real.hasDerivAt_sin s₀).ofReal_comp.mul_const (y 2))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv0 s)).congr_deriv ?_
      rw [hv2 s₀]
      push_cast
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (hasDerivAt_const s₀ (y 1)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv1 s)
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have h1 : HasDerivAt (fun s : ℝ => -((Real.sin s : ℝ) : ℂ)) (-((Real.cos s₀ : ℝ) : ℂ)) s₀ :=
        (Real.hasDerivAt_sin s₀).ofReal_comp.neg
      have h : HasDerivAt (fun s => -((Real.sin s : ℝ) : ℂ) * y 0 + ((Real.cos s : ℝ) : ℂ) * y 2)
          (-((Real.cos s₀ : ℝ) : ℂ) * y 0 + ((-Real.sin s₀ : ℝ) : ℂ) * y 2) s₀ :=
        (h1.mul_const (y 0)).add ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 2))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv2 s)).congr_deriv ?_
      rw [hv0 s₀]
      push_cast
      ring
  have hfun : (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 0 2 s) q)) =
      fun s => MvPolynomial.eval (v s) q := by
    funext s
    exact hR s q
  rw [hfun, hR]
  refine (hasDerivAt_eval_of_hasDerivAt q v _ s₀ hderiv).congr_deriv ?_
  rw [AxisHarmonics.rotDeriv_apply]
  simp only [map_sub, map_mul, MvPolynomial.eval_X, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, add_zero]
  ring

private theorem hasDerivAt_eval_matrixSubst_planeRotation12 (q : MvPolynomial (Fin 3) ℂ) (y : Fin 3 → ℂ) (s₀ : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 1 2 s) q))
      (MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 1 2 s₀) (AxisHarmonics.rotDeriv 1 2 q))) s₀ := by
  let v : ℝ → Fin 3 → ℂ := fun s i => ∑ l : Fin 3, ((planeRotation 1 2 s l i : ℝ) : ℂ) * y l
  have hR : ∀ (s : ℝ) (p : MvPolynomial (Fin 3) ℂ),
      MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 1 2 s) p) = MvPolynomial.eval (v s) p :=
    fun s p => eval_matrixSubst _ _ _
  have hv1 : ∀ s, v s 1 = ((Real.cos s : ℝ) : ℂ) * y 1 + ((Real.sin s : ℝ) : ℂ) * y 2 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv2 : ∀ s, v s 2 = -((Real.sin s : ℝ) : ℂ) * y 1 + ((Real.cos s : ℝ) : ℂ) * y 2 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hv0 : ∀ s, v s 0 = y 0 := by
    intro s
    simp [v, planeRotation, Fin.sum_univ_three]
  have hderiv : ∀ i, HasDerivAt (fun s => v s i) (![0, v s₀ 2, -v s₀ 1] i) s₀ := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (hasDerivAt_const s₀ (y 0)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv0 s)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h : HasDerivAt (fun s => ((Real.cos s : ℝ) : ℂ) * y 1 + ((Real.sin s : ℝ) : ℂ) * y 2)
          (((-Real.sin s₀ : ℝ) : ℂ) * y 1 + ((Real.cos s₀ : ℝ) : ℂ) * y 2) s₀ :=
        ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 1)).add
          ((Real.hasDerivAt_sin s₀).ofReal_comp.mul_const (y 2))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv1 s)).congr_deriv ?_
      rw [hv2 s₀]
      push_cast
      ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have h1 : HasDerivAt (fun s : ℝ => -((Real.sin s : ℝ) : ℂ)) (-((Real.cos s₀ : ℝ) : ℂ)) s₀ :=
        (Real.hasDerivAt_sin s₀).ofReal_comp.neg
      have h : HasDerivAt (fun s => -((Real.sin s : ℝ) : ℂ) * y 1 + ((Real.cos s : ℝ) : ℂ) * y 2)
          (-((Real.cos s₀ : ℝ) : ℂ) * y 1 + ((-Real.sin s₀ : ℝ) : ℂ) * y 2) s₀ :=
        (h1.mul_const (y 1)).add ((Real.hasDerivAt_cos s₀).ofReal_comp.mul_const (y 2))
      refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hv2 s)).congr_deriv ?_
      rw [hv1 s₀]
      push_cast
      ring
  have hfun : (fun s => MvPolynomial.eval y (AxisHarmonics.matrixSubst (planeRotation 1 2 s) q)) =
      fun s => MvPolynomial.eval (v s) q := by
    funext s
    exact hR s q
  rw [hfun, hR]
  refine (hasDerivAt_eval_of_hasDerivAt q v _ s₀ hderiv).congr_deriv ?_
  rw [AxisHarmonics.rotDeriv_apply]
  simp only [map_sub, map_mul, MvPolynomial.eval_X, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero]
  ring

private def planes : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

private noncomputable def rot (c₁ c₂ : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := planeRotation c₁ c₂ s

private def val {E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)} (F : E) : Matrix (Fin 3) (Fin 3) ℝ → ℂ :=
  (F : Matrix (Fin 3) (Fin 3) ℝ → ℂ)

private theorem rot_planes_mem (c : Fin 3) (s : ℝ) :
    rot (planes c).1 (planes c).2 s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  fin_cases c
  · exact planeRotation_zero_one_mem s
  · exact planeRotation_zero_two_mem s
  · exact planeRotation_one_two_mem s

private theorem rot_planes_add (c : Fin 3) (s t : ℝ) :
    rot (planes c).1 (planes c).2 (s + t) = rot (planes c).1 (planes c).2 s * rot (planes c).1 (planes c).2 t := by
  fin_cases c
  · exact planeRotation_zero_one_add s t
  · exact planeRotation_zero_two_add s t
  · exact planeRotation_one_two_add s t

private theorem rot_planes_zero (c : Fin 3) : rot (planes c).1 (planes c).2 0 = 1 := by
  fin_cases c
  · exact planeRotation_zero_one_zero
  · exact planeRotation_zero_two_zero
  · exact planeRotation_one_two_zero

private theorem rot_planes_two_pi (c : Fin 3) : rot (planes c).1 (planes c).2 (2 * Real.pi) = 1 := by
  fin_cases c
  · exact planeRotation_zero_one_two_pi
  · exact planeRotation_zero_two_two_pi
  · exact planeRotation_one_two_two_pi

private noncomputable def groupRestrict (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) :
    E →ₗ[ℂ] (Matrix.orthogonalGroup (Fin 3) ℝ → ℂ) where
  toFun F := fun g => val F (g : Matrix (Fin 3) (Fin 3) ℝ)
  map_add' F F' := by
    funext g
    simp [val]
  map_smul' a F := by
    funext g
    simp [val]

private noncomputable def groupKernel (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) : Submodule ℂ E :=
  LinearMap.ker (groupRestrict E)

private theorem mem_groupKernel {E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)} {F : E} :
    F ∈ groupKernel E ↔ ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, val F r = 0 := by
  constructor
  · intro h r hr
    exact congrFun (LinearMap.mem_ker.mp h) ⟨r, hr⟩
  · intro h
    rw [groupKernel, LinearMap.mem_ker]
    funext g
    exact h g g.2

private noncomputable def groupEval (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) :
    (E ⧸ groupKernel E) →ₗ[ℂ] (Matrix.orthogonalGroup (Fin 3) ℝ → ℂ) :=
  (groupKernel E).liftQ (groupRestrict E) le_rfl

private theorem groupEval_mk (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (F : E)
    (g : Matrix.orthogonalGroup (Fin 3) ℝ) :
    groupEval E ((groupKernel E).mkQ F) g = val F g := by
  simp [groupEval, groupRestrict]

private theorem groupEval_injective (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) :
    Function.Injective (groupEval E) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

private theorem eq_zero_of_forall_groupEval {E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)} {v : E ⧸ groupKernel E}
    (h : ∀ g, groupEval E v g = 0) : v = 0 := by
  apply groupEval_injective E
  funext g
  rw [map_zero]
  exact h g

private theorem exists_groupEval_ne_zero {E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)} {v : E ⧸ groupKernel E}
    (hv : v ≠ 0) : ∃ g, groupEval E v g ≠ 0 := by
  by_contra h
  exact hv (eq_zero_of_forall_groupEval fun g => not_not.mp (not_exists.mp h g))

private theorem groupQuotient_nontrivial (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ))
    (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0) : Nontrivial (E ⧸ groupKernel E) := by
  obtain ⟨F, hF, r, hr, hFr⟩ := hne
  refine ⟨⟨(groupKernel E).mkQ ⟨F, hF⟩, 0, fun h => hFr ?_⟩⟩
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_groupKernel] at h
  exact h r hr

private theorem exists_mem_eq_groupEval (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (v : E ⧸ groupKernel E) :
    ∃ F ∈ E, ∀ r, ∀ hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r = groupEval E v ⟨r, hr⟩ := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  exact ⟨F, F.2, fun r hr => (groupEval_mk E F ⟨r, hr⟩).symm⟩

private noncomputable def descend (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (A : Module.End ℂ E)
    (hA : ∀ F ∈ groupKernel E, A F ∈ groupKernel E) : Module.End ℂ (E ⧸ groupKernel E) :=
  (groupKernel E).mapQ (groupKernel E) A fun F hF => hA F hF

private theorem descend_mk (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (A : Module.End ℂ E)
    (hA : ∀ F ∈ groupKernel E, A F ∈ groupKernel E) (F : E) :
    descend E A hA ((groupKernel E).mkQ F) = (groupKernel E).mkQ (A F) := by
  simp [descend]

private theorem mkQ_eq_mkQ_of_forall {E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)} {F F' : E}
    (h : ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      val F r = val F' r) :
    (groupKernel E).mkQ F = (groupKernel E).mkQ F' := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_groupKernel]
  intro r hr
  show val F r - val F' r = 0
  rw [h r hr, sub_self]

section operators

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (L : Fin 3 → Module.End ℂ E)
variable (htie :
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0))

include htie in
private theorem op_mem_groupKernel (c : Fin 3) {F : E} (hF : F ∈ groupKernel E) : L c F ∈ groupKernel E := by
  rw [mem_groupKernel] at hF ⊢
  intro r hr
  have h := htie F c r hr
  have hz : (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) = fun _ => (0 : ℂ) := by
    funext s
    exact hF _ (orthogonal_mul_mem hr (rot_planes_mem c s))
  rw [hz] at h
  exact h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

private noncomputable def descendedOp (c : Fin 3) : Module.End ℂ (E ⧸ groupKernel E) :=
  descend E (L c) fun _ hF => op_mem_groupKernel E L htie c hF

private theorem descendedOp_mk (c : Fin 3) (F : E) :
    descendedOp E L htie c ((groupKernel E).mkQ F) = (groupKernel E).mkQ (L c F) :=
  descend_mk E (L c) _ F

include htie in

private theorem hasDerivAt_member_flow (F : E) (c : Fin 3) {r : Matrix (Fin 3) (Fin 3) ℝ}
    (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s))
      (val (L c F) (r * rot (planes c).1 (planes c).2 s₀)) s₀ := by
  have h0 := htie F c (r * rot (planes c).1 (planes c).2 s₀) (orthogonal_mul_mem hr (rot_planes_mem c s₀))
  have h1 : HasDerivAt (fun t : ℝ => val F (r * rot (planes c).1 (planes c).2 s₀ * rot (planes c).1 (planes c).2 t))
      (val (L c F) (r * rot (planes c).1 (planes c).2 s₀)) ((fun s : ℝ => s - s₀) s₀) := by
    simp only [sub_self]
    exact h0
  have h2 : HasDerivAt (fun s : ℝ => s - s₀) 1 s₀ := (hasDerivAt_id s₀).sub_const s₀
  have h3 := HasDerivAt.scomp (h := fun s : ℝ => s - s₀) s₀ h1 h2
  rw [one_smul] at h3
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show val F (r * rot (planes c).1 (planes c).2 s) =
    val F (r * rot (planes c).1 (planes c).2 s₀ * rot (planes c).1 (planes c).2 (s - s₀))
  have hs : s₀ + (s - s₀) = s := by ring
  rw [Matrix.mul_assoc, ← rot_planes_add c, hs]

private noncomputable def flowPoint (c : Fin 3) (g : Matrix.orthogonalGroup (Fin 3) ℝ) (s : ℝ) :
    Matrix.orthogonalGroup (Fin 3) ℝ :=
  ⟨(g : Matrix (Fin 3) (Fin 3) ℝ) * rot (planes c).1 (planes c).2 s, orthogonal_mul_mem g.2 (rot_planes_mem c s)⟩

private theorem flowPoint_zero (c : Fin 3) (g : Matrix.orthogonalGroup (Fin 3) ℝ) : flowPoint c g 0 = g := by
  apply Subtype.ext
  simp [flowPoint, rot_planes_zero]

private theorem flowPoint_two_pi (c : Fin 3) (g : Matrix.orthogonalGroup (Fin 3) ℝ) :
    flowPoint c g (2 * Real.pi) = g := by
  apply Subtype.ext
  simp [flowPoint, rot_planes_two_pi]

private theorem hasDerivAt_groupEval_flowPoint (v : E ⧸ groupKernel E) (c : Fin 3)
    (g : Matrix.orthogonalGroup (Fin 3) ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => groupEval E v (flowPoint c g s))
      (groupEval E (descendedOp E L htie c v) (flowPoint c g s₀)) s₀ := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  rw [descendedOp_mk]
  simp only [groupEval_mk, flowPoint]
  exact hasDerivAt_member_flow E L htie F c g.2 s₀

private theorem eigenvalue_descendedOp_eq_int_mul_I (c : Fin 3) (μ : ℂ) (v : E ⧸ groupKernel E) (hv : v ≠ 0)
    (hμ : descendedOp E L htie c v = μ • v) : ∃ n : ℤ, μ = n * Complex.I := by
  obtain ⟨g, hg⟩ := exists_groupEval_ne_zero hv
  let f : ℝ → ℂ := fun s => groupEval E v (flowPoint c g s)
  have hf : ∀ s, HasDerivAt f (μ * f s) s := by
    intro s
    have h := hasDerivAt_groupEval_flowPoint E L htie v c g s
    rw [hμ, map_smul, Pi.smul_apply, smul_eq_mul] at h
    exact h
  let d : ℝ → ℂ := fun s => f s - Complex.exp (μ * s) * f 0
  have hexp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (μ * s)) (Complex.exp (μ * s) * μ) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).ofReal_comp
    have h2 := h1.const_mul μ
    rw [mul_one] at h2
    exact h2.cexp
  have hd : ∀ s, HasDerivAt d (μ * d s) s := by
    intro s
    have h := (hf s).sub ((hexp s).mul_const (f 0))
    refine h.congr_deriv ?_
    simp only [d]
    ring
  have hd0 : d 0 = 0 := by
    simp [d]
  have hdzero : d = fun _ => 0 := by
    let y : ℝ → Fin 1 → ℂ := fun s _ => d s
    have hy : ∀ s, HasDerivAt y ((Matrix.of fun _ _ : Fin 1 => μ).mulVec (y s)) s := by
      intro s
      rw [hasDerivAt_pi]
      intro i
      have hi : (Matrix.of fun _ _ : Fin 1 => μ).mulVec (y s) i = μ * d s := by
        simp [Matrix.mulVec, dotProduct, y]
      rw [hi]
      exact hd s
    have hy0 : y 0 = 0 := by
      funext i
      simp [y, hd0]
    have h := linearSystem_eq_zero _ y hy hy0
    funext s
    exact congrFun (congrFun h s) 0
  have hper : f (2 * Real.pi) = f 0 := by
    simp only [f, flowPoint_two_pi, flowPoint_zero]
  have h2 : Complex.exp (μ * ((2 * Real.pi : ℝ) : ℂ)) * f 0 = f 0 := by
    have h := congrFun hdzero (2 * Real.pi)
    simp only [d, sub_eq_zero] at h
    rw [← h, hper]
  have hf0 : f 0 ≠ 0 := by
    simpa only [f, flowPoint_zero] using hg
  have hexp1 : Complex.exp (μ * ((2 * Real.pi : ℝ) : ℂ)) = 1 :=
    mul_right_cancel₀ hf0 (h2.trans (one_mul (f 0)).symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  refine ⟨n, ?_⟩
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  apply mul_right_cancel₀ h2π
  rw [hn]
  push_cast
  ring

end operators
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

section relations

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (L : Fin 3 → Module.End ℂ E)
variable (htie :
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0))
variable (hrel :
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r))

include hrel in

private theorem descendedOp_comm_01 (v : E ⧸ groupKernel E) :
    descendedOp E L htie 0 (descendedOp E L htie 1 v) - descendedOp E L htie 1 (descendedOp E L htie 0 v) =
      descendedOp E L htie 2 v := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  simp only [descendedOp_mk]
  rw [← map_sub]
  apply mkQ_eq_mkQ_of_forall
  intro r hr
  have hh := (hrel F r hr).1
  simp only [val, Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply] at hh ⊢
  first | exact hh | simpa using hh

include hrel in
private theorem descendedOp_comm_02 (v : E ⧸ groupKernel E) :
    descendedOp E L htie 0 (descendedOp E L htie 2 v) - descendedOp E L htie 2 (descendedOp E L htie 0 v) =
      - descendedOp E L htie 1 v := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  simp only [descendedOp_mk]
  rw [← map_sub, ← map_neg]
  apply mkQ_eq_mkQ_of_forall
  intro r hr
  have hh := (hrel F r hr).2.1
  simp only [val, Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply] at hh ⊢
  first | exact hh | simpa using hh

include hrel in
private theorem descendedOp_comm_12 (v : E ⧸ groupKernel E) :
    descendedOp E L htie 1 (descendedOp E L htie 2 v) - descendedOp E L htie 2 (descendedOp E L htie 1 v) =
      descendedOp E L htie 0 v := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  simp only [descendedOp_mk]
  rw [← map_sub]
  apply mkQ_eq_mkQ_of_forall
  intro r hr
  have hh := (hrel F r hr).2.2
  simp only [val, Submodule.coe_sub, Submodule.coe_neg, Pi.sub_apply, Pi.neg_apply] at hh ⊢
  first | exact hh | simpa using hh

end relations
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

section translation

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ))
variable
    (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E)

private noncomputable def negTranslate : Module.End ℂ E where
  toFun F := ⟨fun r => val F (r * (-1)), hstab F F.2 (-1) neg_one_mem_orthogonal⟩
  map_add' F F' := by
    apply Subtype.ext
    funext r
    simp [val]
  map_smul' a F := by
    apply Subtype.ext
    funext r
    simp [val]

private theorem negTranslate_coe (F : E) (r : Matrix (Fin 3) (Fin 3) ℝ) :
    val (negTranslate E hstab F) r = val F (r * (-1)) :=
  rfl

private theorem negTranslate_mem_groupKernel {F : E} (hF : F ∈ groupKernel E) :
    negTranslate E hstab F ∈ groupKernel E := by
  rw [mem_groupKernel] at hF ⊢
  intro r hr
  rw [negTranslate_coe]
  exact hF _ (orthogonal_mul_mem hr neg_one_mem_orthogonal)

private noncomputable def descendedNeg : Module.End ℂ (E ⧸ groupKernel E) :=
  descend E (negTranslate E hstab) fun _ hF => negTranslate_mem_groupKernel E hstab hF

private theorem descendedNeg_mk (F : E) :
    descendedNeg E hstab ((groupKernel E).mkQ F) = (groupKernel E).mkQ (negTranslate E hstab F) :=
  descend_mk E _ _ F

private noncomputable def negOneG : Matrix.orthogonalGroup (Fin 3) ℝ := ⟨-1, neg_one_mem_orthogonal⟩

private theorem groupEval_descendedNeg (v : E ⧸ groupKernel E) (g : Matrix.orthogonalGroup (Fin 3) ℝ) :
    groupEval E (descendedNeg E hstab v) g = groupEval E v (g * negOneG) := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  rw [descendedNeg_mk, groupEval_mk, groupEval_mk, negTranslate_coe]
  rfl

private theorem negOneG_mul_negOneG (g : Matrix.orthogonalGroup (Fin 3) ℝ) : g * negOneG * negOneG = g := by
  apply Subtype.ext
  show (g : Matrix (Fin 3) (Fin 3) ℝ) * (-1) * (-1) = g
  rw [Matrix.mul_assoc, (neg_one_mul (-1 : Matrix (Fin 3) (Fin 3) ℝ)).trans (neg_neg 1), Matrix.mul_one]

private theorem descendedNeg_descendedNeg (v : E ⧸ groupKernel E) :
    descendedNeg E hstab (descendedNeg E hstab v) = v := by
  apply groupEval_injective E
  funext g
  rw [groupEval_descendedNeg, groupEval_descendedNeg, negOneG_mul_negOneG]

variable (L : Fin 3 → Module.End ℂ E)
variable (htie :
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0))

private theorem descendedNeg_comm_descendedOp (c : Fin 3) (v : E ⧸ groupKernel E) :
    descendedNeg E hstab (descendedOp E L htie c v) = descendedOp E L htie c (descendedNeg E hstab v) := by
  obtain ⟨F, rfl⟩ := (groupKernel E).mkQ_surjective v
  rw [descendedOp_mk, descendedNeg_mk, descendedNeg_mk, descendedOp_mk]
  apply mkQ_eq_mkQ_of_forall
  intro r hr
  rw [negTranslate_coe]
  have h1 := htie (negTranslate E hstab F) c r hr
  have h2 := htie F c (r * (-1)) (orthogonal_mul_mem hr neg_one_mem_orthogonal)
  have hfun : (fun s : ℝ => val (negTranslate E hstab F) (r * rot (planes c).1 (planes c).2 s)) =
      fun s : ℝ => val F (r * (-1) * rot (planes c).1 (planes c).2 s) := by
    funext s
    rw [negTranslate_coe, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_assoc, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg]
  rw [hfun] at h1
  exact h2.unique h1

end translation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private theorem rot_planes_det (c : Fin 3) (s : ℝ) : (rot (planes c).1 (planes c).2 s).det = 1 := by
  fin_cases c
  · exact planeRotation_zero_one_det s
  · exact planeRotation_zero_two_det s
  · exact planeRotation_one_two_det s

section abstractModel

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

private def evalAt (m : M) : (M →ₗ[ℂ] N) →ₗ[ℂ] N where
  toFun T := T m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalAt_apply (m : M) (T : M →ₗ[ℂ] N) : evalAt m T = T m := rfl

private def precomp (f : M →ₗ[ℂ] M) : (M →ₗ[ℂ] N) →ₗ[ℂ] (M →ₗ[ℂ] N) where
  toFun T := T.comp f
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

private theorem precomp_apply (f : M →ₗ[ℂ] M) (T : M →ₗ[ℂ] N) (m : M) : precomp f T m = T (f m) := rfl

end abstractModel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private def evalPoint (g : Matrix.orthogonalGroup (Fin 3) ℝ) : (Matrix.orthogonalGroup (Fin 3) ℝ → ℂ) →ₗ[ℂ] ℂ where
  toFun f := f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section identification

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Matrix (Fin 3) (Fin 3) ℝ → Module.End ℂ W) (Dc : Fin 3 → Module.End ℂ W)
variable (ev : V →ₗ[ℂ] (Matrix.orthogonalGroup (Fin 3) ℝ → ℂ)) (Lb : Fin 3 → Module.End ℂ V)
variable (S' : Submodule ℂ W) (ι : S' →ₗ[ℂ] V) (a : ℕ)

private noncomputable def twisted (k : Matrix (Fin 3) (Fin 3) ℝ) : Module.End ℂ W :=
  ((k.det : ℝ) : ℂ) ^ a • ρ k

private theorem twisted_apply (k : Matrix (Fin 3) (Fin 3) ℝ) (w : W) :
    twisted ρ a k w = ((k.det : ℝ) : ℂ) ^ a • ρ k w :=
  rfl

private def Claim (k : Matrix.orthogonalGroup (Fin 3) ℝ) : Prop :=
  ∀ z : S', ∃ z' : S', (z' : W) = twisted ρ a k z ∧
    ∀ g : Matrix.orthogonalGroup (Fin 3) ℝ, ev (ι z) (g * k) = ev (ι z') g

variable (hmul : ∀ x y : Matrix (Fin 3) (Fin 3) ℝ, ρ (x * y) = (ρ x).comp (ρ y))

include hmul in
private theorem twisted_mul (x y : Matrix (Fin 3) (Fin 3) ℝ) (w : W) :
    twisted ρ a (x * y) w = twisted ρ a x (twisted ρ a y w) := by
  simp only [twisted_apply, hmul x y, LinearMap.comp_apply, Matrix.det_mul, map_smul, smul_smul]
  push_cast
  rw [mul_pow, mul_comm]

include hmul in

private theorem claim_mul {x y : Matrix.orthogonalGroup (Fin 3) ℝ} (hx : Claim ρ ev S' ι a x)
    (hy : Claim ρ ev S' ι a y) : Claim ρ ev S' ι a (x * y) := by
  intro z
  obtain ⟨z₁, hz₁, h₁⟩ := hy z
  obtain ⟨z₂, hz₂, h₂⟩ := hx z₁
  refine ⟨z₂, ?_, fun g => ?_⟩
  · rw [hz₂, hz₁, Submonoid.coe_mul, twisted_mul ρ a hmul]
  · rw [← mul_assoc, h₁ (g * x), h₂ g]

variable (hS : ∀ c : Fin 3, ∀ z ∈ S', Dc c z ∈ S')

private def stringStabilizer : Submodule ℂ (Module.End ℂ W) where
  carrier := {T | ∀ z ∈ S', T z ∈ S'}
  zero_mem' := fun z _ => by simp
  add_mem' := fun {T T'} hT hT' z hz => by simpa using S'.add_mem (hT z hz) (hT' z hz)
  smul_mem' := fun b {T} hT z hz => by simpa using S'.smul_mem b (hT z hz)

private theorem mem_stringStabilizer {T : Module.End ℂ W} : T ∈ stringStabilizer S' ↔ ∀ z ∈ S', T z ∈ S' :=
  Iff.rfl

variable [FiniteDimensional ℂ W]

variable (hone : ρ 1 = LinearMap.id)
variable (ΦW : Set (Module.Dual ℂ W)) (hΦW : ∀ w : W, (∀ φ ∈ ΦW, φ w = 0) → w = 0)
variable (hflowW : ∀ φ ∈ ΦW, ∀ (c : Fin 3) (w : W) (s₀ : ℝ),
  HasDerivAt (fun s : ℝ => φ (ρ (rot (planes c).1 (planes c).2 s) w))
    (φ (ρ (rot (planes c).1 (planes c).2 s₀) (Dc c w))) s₀)

include hΦW hflowW in

private theorem hasDerivAt_flow_dual (c : Fin 3) (Ψ : Module.Dual ℂ (Module.End ℂ W)) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => Ψ (ρ (rot (planes c).1 (planes c).2 s)))
      (Ψ (precomp (Dc c) (ρ (rot (planes c).1 (planes c).2 s₀)))) s₀ := by
  let ΦY : Set (Module.Dual ℂ (Module.End ℂ W)) := {ψ | ∃ φ ∈ ΦW, ∃ w : W, ψ = φ.comp (evalAt w)}
  have hΦY : ∀ T : Module.End ℂ W, (∀ ψ ∈ ΦY, ψ T = 0) → T = 0 := by
    intro T hT
    apply LinearMap.ext
    intro w
    apply hΦW
    intro φ hφ
    exact hT _ ⟨φ, hφ, w, rfl⟩
  refine hasDerivAt_dual_of_separating ΦY hΦY (fun s => ρ (rot (planes c).1 (planes c).2 s)) _ s₀ ?_ Ψ
  rintro ψ ⟨φ, hφ, w, rfl⟩
  simp only [LinearMap.comp_apply, evalAt_apply, precomp_apply]
  exact hflowW φ hφ c w s₀

include hone hΦW hflowW hS in

private theorem flow_mem_stringStabilizer (c : Fin 3) (s : ℝ) :
    ρ (rot (planes c).1 (planes c).2 s) ∈ stringStabilizer S' := by
  refine mem_of_hasDerivAt_of_mapsTo (stringStabilizer S') (precomp (Dc c)) ?_
    (fun s => ρ (rot (planes c).1 (planes c).2 s)) ?_ ?_ s
  · intro T hT z hz
    rw [precomp_apply]
    exact hT _ (hS c z hz)
  · intro Ψ t
    exact hasDerivAt_flow_dual ρ Dc ΦW hΦW hflowW c Ψ t
  · show ρ (rot (planes c).1 (planes c).2 0) ∈ stringStabilizer S'
    rw [rot_planes_zero, hone]
    intro z hz
    simpa using hz

variable (hflowV : ∀ (v : V) (c : Fin 3) (g : Matrix.orthogonalGroup (Fin 3) ℝ) (s₀ : ℝ),
  HasDerivAt (fun s : ℝ => ev v (flowPoint c g s)) (ev (Lb c v) (flowPoint c g s₀)) s₀)
variable (hι : ∀ (c : Fin 3) (z : S'), Lb c (ι z) = ι ((Dc c).restrict (hS c) z))

include hone hΦW hflowW hS hflowV hι in

private theorem claim_flow (c : Fin 3) (s : ℝ) :
    Claim ρ ev S' ι a ⟨rot (planes c).1 (planes c).2 s, rot_planes_mem c s⟩ := by
  intro z
  have hstab := flow_mem_stringStabilizer ρ Dc S' hS hone ΦW hΦW hflowW c s
  refine ⟨⟨ρ (rot (planes c).1 (planes c).2 s) z, hstab z z.2⟩, ?_, fun g => ?_⟩
  · rw [twisted_apply, rot_planes_det, Complex.ofReal_one, one_pow, one_smul]

  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend ((evalPoint g).comp (ev.comp ι))
  have hlam' : ∀ z : S', lam z = ev (ι z) g := fun z => LinearMap.congr_fun hlam z

  let d : ℝ → Module.Dual ℂ S' := fun u =>
    (evalPoint (flowPoint c g u)).comp (ev.comp ι) - lam.comp ((ρ (rot (planes c).1 (planes c).2 u)).comp S'.subtype)
  have hd_apply : ∀ (u : ℝ) (z : S'),
      d u z = ev (ι z) (flowPoint c g u) - lam (ρ (rot (planes c).1 (planes c).2 u) z) := fun u z => rfl
  have hd : ∀ u, d u ∈ (⊥ : Submodule ℂ (Module.Dual ℂ S')) := by
    intro u
    refine mem_of_hasDerivAt_of_mapsTo ⊥ (precomp ((Dc c).restrict (hS c))) ?_ d ?_ ?_ u
    · intro θ hθ
      rw [Submodule.mem_bot] at hθ ⊢
      rw [hθ, map_zero]
    · intro Ψ t
      let ΦD : Set (Module.Dual ℂ (Module.Dual ℂ S')) := {ψ | ∃ z : S', ψ = evalAt z}
      have hΦD : ∀ θ : Module.Dual ℂ S', (∀ ψ ∈ ΦD, ψ θ = 0) → θ = 0 := by
        intro θ hθ
        apply LinearMap.ext
        intro z
        exact hθ _ ⟨z, rfl⟩
      refine hasDerivAt_dual_of_separating ΦD hΦD d _ t ?_ Ψ
      rintro ψ ⟨z, rfl⟩
      simp only [evalAt_apply, hd_apply, precomp_apply]
      have h1 := hflowV (ι z) c g t
      rw [hι c z] at h1
      have h2 := hasDerivAt_flow_dual ρ Dc ΦW hΦW hflowW c (lam.comp (evalAt (z : W))) t
      simp only [LinearMap.comp_apply, evalAt_apply, precomp_apply] at h2
      have h3 := h1.sub h2
      rw [LinearMap.coe_restrict_apply]
      exact h3
    · rw [Submodule.mem_bot]
      apply LinearMap.ext
      intro z
      rw [hd_apply, flowPoint_zero, rot_planes_zero, hone, LinearMap.id_apply, hlam' z, sub_self, LinearMap.zero_apply]
  have hds := hd s
  rw [Submodule.mem_bot] at hds
  have h := hd_apply s z
  rw [hds, LinearMap.zero_apply, eq_comm, sub_eq_zero] at h
  show ev (ι z) (flowPoint c g s) = _
  rw [h]
  exact hlam' ⟨ρ (rot (planes c).1 (planes c).2 s) z, hstab z z.2⟩

variable (hneg : Claim ρ ev S' ι a negOneG)

include hmul hone hΦW hflowW hS hflowV hι hneg in

private theorem claim_all (k : Matrix.orthogonalGroup (Fin 3) ℝ) : Claim ρ ev S' ι a k := by
  have key : ∀ m : Matrix (Fin 3) (Fin 3) ℝ, ∀ hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      Claim ρ ev S' ι a ⟨m, hm⟩ := by
    refine fun m hm => orthogonal_induction
      (fun m => ∀ hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ, Claim ρ ev S' ι a ⟨m, hm⟩)
      (fun s _ => ?_) (fun s _ => ?_) (fun _ => hneg) (fun x y hx hy Px Py _ => ?_) m hm hm
    · exact claim_flow ρ Dc ev Lb S' ι a hS hone ΦW hΦW hflowW hflowV hι 0 s
    · exact claim_flow ρ Dc ev Lb S' ι a hS hone ΦW hΦW hflowW hflowV hι 2 s
    · exact claim_mul ρ ev S' ι a hmul (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (Px hx) (Py hy)
  exact key k k.2

include hmul hone hΦW hflowW hS hflowV hι hneg in

private theorem eval_eq_twisted (lam : Module.Dual ℂ W) (hlam : ∀ z : S', lam z = ev (ι z) 1)
    (k : Matrix.orthogonalGroup (Fin 3) ℝ) (z : S') :
    ev (ι z) k = (((k : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) ^ a * lam (ρ k z) := by
  obtain ⟨z', hz', h⟩ := claim_all ρ Dc ev Lb S' ι a hmul hS hone ΦW hΦW hflowW hflowV hι hneg k z
  have h1 := h 1
  rw [one_mul] at h1
  rw [h1, ← hlam z', hz', twisted_apply, map_smul, smul_eq_mul]

end identification
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

noncomputable section

open MvPolynomial

namespace AxisHarmonics

section axisTriple

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private def axisH (R : Module.End ℂ M) : Module.End ℂ M := (2 * Complex.I) • R
private def axisE (A B : Module.End ℂ M) : Module.End ℂ M := A + Complex.I • B
private def axisF (A B : Module.End ℂ M) : Module.End ℂ M := - A + Complex.I • B

variable (R A B : Module.End ℂ M)
variable (hAB : ∀ w, A (B w) - B (A w) = R w) (hRA : ∀ w, R (A w) - A (R w) = B w)
  (hRB : ∀ w, R (B w) - B (R w) = - A w)

include hAB in
private lemma axisE_axisF_comm : ⁅axisE A B, axisF A B⁆ = axisH R := by
  refine LinearMap.ext (fun w => ?_)
  change (axisE A B * axisF A B - axisF A B * axisE A B) w = axisH R w
  have h1 := hAB w
  simp only [axisE, axisF, axisH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, map_add, map_neg, map_smul]
  linear_combination (norm := module) (2 * Complex.I) • h1

include hRA hRB in
private lemma axisH_axisE_comm : ⁅axisH R, axisE A B⁆ = 2 • axisE A B := by
  refine LinearMap.ext (fun w => ?_)
  change (axisH R * axisE A B - axisE A B * axisH R) w = (2 • axisE A B) w
  have h1 := hRA w
  have h2 := hRB w
  simp only [axisE, axisH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, smul_smul]
  linear_combination (norm := module) (2 * Complex.I) • h1 + (-2 : ℂ) • h2 +
    Complex.I_mul_I • ((2 : ℂ) • (R (B w) - B (R w)))

include hRA hRB in
private lemma axisH_axisF_comm : ⁅axisH R, axisF A B⁆ = -(2 • axisF A B) := by
  refine LinearMap.ext (fun w => ?_)
  change (axisH R * axisF A B - axisF A B * axisH R) w = (-(2 • axisF A B)) w
  have h1 := hRA w
  have h2 := hRB w
  simp only [axisF, axisH, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, map_add, map_neg, map_smul, smul_smul]
  linear_combination (norm := module) (-(2 * Complex.I)) • h1 + (-2 : ℂ) • h2 +
    Complex.I_mul_I • ((2 : ℂ) • (R (B w) - B (R w)))

include hAB hRA hRB in
private lemma isSl2Triple_axisTriple (hR : axisH R ≠ 0) : IsSl2Triple (axisH R) (axisE A B) (axisF A B) where
  h_ne_zero := hR
  lie_e_f := axisE_axisF_comm R A B hAB
  lie_h_e_nsmul := axisH_axisE_comm R A B hRA hRB
  lie_h_f_nsmul := axisH_axisF_comm R A B hRA hRB

private def coordR (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) := (-Complex.I / 2) • coordH n
private def coordA (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) := (1 / 2 : ℂ) • (coordE n - coordF n)
private def coordB (n : ℕ) : Module.End ℂ (Fin (n + 1) → ℂ) := (-Complex.I / 2) • (coordE n + coordF n)

variable {R A B} {n : ℕ} (Φ : (Fin (n + 1) → ℂ) →ₗ[ℂ] M)
variable (hΦH : ∀ a, Φ (coordH n a) = axisH R (Φ a)) (hΦE : ∀ a, Φ (coordE n a) = axisE A B (Φ a))
  (hΦF : ∀ a, Φ (coordF n a) = axisF A B (Φ a))

include hΦH in
private lemma intertwine_coordR (a : Fin (n + 1) → ℂ) : Φ (coordR n a) = R (Φ a) := by
  rw [coordR, LinearMap.smul_apply, map_smul, hΦH, axisH, LinearMap.smul_apply, smul_smul]
  have hc : -Complex.I / 2 * (2 * Complex.I) = 1 := by linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [hc, one_smul]

include hΦE hΦF in
private lemma intertwine_coordA (a : Fin (n + 1) → ℂ) : Φ (coordA n a) = A (Φ a) := by
  rw [coordA, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, hΦE, hΦF, axisE, axisF]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply]
  module

include hΦE hΦF in
private lemma intertwine_coordB (a : Fin (n + 1) → ℂ) : Φ (coordB n a) = B (Φ a) := by
  rw [coordB, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, hΦE, hΦF, axisE, axisF]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply]
  linear_combination (norm := module) Complex.I_mul_I • ((-1 : ℂ) • B (Φ a))

end axisTriple
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private def axisKind (j c : Fin 3) : Fin 3 := ![![1, 2, 0], ![1, 0, 2], ![0, 1, 2]] j c
private def axisSign (j c : Fin 3) : ℂ := ![![-1, -1, 1], ![1, 1, -1], ![1, 1, 1]] j c

private def coordPlane (n : ℕ) (j c : Fin 3) : Module.End ℂ (Fin (n + 1) → ℂ) :=
  axisSign j c • ![coordR n, coordA n, coordB n] (axisKind j c)

private lemma planeEnd_eq_table (ℓ : ℕ) (j c : Fin 3) :
    planeEnd ℓ c = axisSign j c • ![axisRotEnd ℓ j, liftAEnd ℓ j, liftBEnd ℓ j] (axisKind j c) := by
  refine LinearMap.ext (fun w => Subtype.ext ?_)
  fin_cases j <;> fin_cases c <;>
    simp only [axisKind, axisSign, planeEnd, axisRotEnd, liftAEnd, liftBEnd, planeDeriv, planeOf, axisRot, liftA,
      liftB, axisA, axisB, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, LinearMap.smul_apply, one_smul,
      neg_smul, Submodule.coe_neg, restrictDeg_coe] <;>
    first
    | rfl
    | rw [rotDeriv_swap, Derivation.neg_apply]

private lemma intertwine_coordPlane {M : Type*} [AddCommGroup M] [Module ℂ M] {R A B : Module.End ℂ M}
    (Lop : Fin 3 → Module.End ℂ M) (j : Fin 3)
    (htable : ∀ c, Lop c = axisSign j c • ![R, A, B] (axisKind j c)) {n : ℕ} (Φ : (Fin (n + 1) → ℂ) →ₗ[ℂ] M)
    (hΦH : ∀ a, Φ (coordH n a) = axisH R (Φ a)) (hΦE : ∀ a, Φ (coordE n a) = axisE A B (Φ a))
    (hΦF : ∀ a, Φ (coordF n a) = axisF A B (Φ a)) (c : Fin 3) (a : Fin (n + 1) → ℂ) :
    Φ (coordPlane n j c a) = Lop c (Φ a) := by
  rw [htable c, coordPlane, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  congr 1
  generalize axisKind j c = t
  fin_cases t
  · exact intertwine_coordR Φ hΦH a
  · exact intertwine_coordA Φ hΦE hΦF a
  · exact intertwine_coordB Φ hΦE hΦF a

private lemma stringMap_single {M : Type*} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) (z : M) (n : ℕ)
    (i : Fin (n + 1)) : stringMap f z n (Pi.single i 1) = stringVec f z n i := by
  rw [stringMap_apply]
  simp [Pi.single_apply]

private lemma stringMap_apply_of_eq_zero {M : Type*} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) (z : M)
    {n : ℕ} (hn : n = 0) (a : Fin (n + 1) → ℂ) : stringMap f z n a = a ⟨0, by omega⟩ • z := by
  rw [stringMap_apply, Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [stringVec]
  · intro i _ hi
    exact absurd (Fin.ext (by have := i.isLt; omega)) hi
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma coordPlane_zero (j c : Fin 3) : coordPlane 0 j c = 0 := by
  have hH : coordH 0 = 0 := LinearMap.ext (fun a => funext (fun i => by simp [coordH_apply]))
  have hE : coordE 0 = 0 := LinearMap.ext (fun a => funext (fun i => by
    have hi : i = Fin.last 0 := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hi, coordE_apply_last]; rfl))
  have hF : coordF 0 = 0 := LinearMap.ext (fun a => funext (fun i => by
    have hi : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [hi, coordF_apply_zero]; rfl))
  have h0 : (![coordR 0, coordA 0, coordB 0] : Fin 3 → Module.End ℂ (Fin (0 + 1) → ℂ)) (axisKind j c) = 0 := by
    generalize axisKind j c = t
    fin_cases t <;> simp [coordR, coordA, coordB, hH, hE, hF]
  rw [coordPlane, h0, smul_zero]

section polynomialSide

variable (ℓ : ℕ) (j : Fin 3)

private def polyString : (Fin (2 * ℓ + 1) → ℂ) →ₗ[ℂ] HomogP ℓ := stringMap (tripleF ℓ j) (highestVec ℓ j) (2 * ℓ)

private def zonalIndex : Fin (2 * ℓ + 1) := ⟨ℓ, by omega⟩

private lemma lapL_liftA (j : Fin 3) (q : CoeffP) : lapL (liftA j q) = liftA j (lapL q) := lapL_rotDeriv _ _ q
private lemma lapL_liftB (j : Fin 3) (q : CoeffP) : lapL (liftB j q) = liftB j (lapL q) := lapL_rotDeriv _ _ q

private lemma tripleF_coe (w : HomogP ℓ) :
    ((tripleF ℓ j w : HomogP ℓ) : CoeffP) = - liftA j (w : CoeffP) + Complex.I • liftB j (w : CoeffP) := by
  simp only [tripleF, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Submodule.coe_add,
    Submodule.coe_neg, Submodule.coe_smul, liftAEnd, liftBEnd, restrictDeg_coe]

private lemma lapL_stringVec (i : Fin (2 * ℓ + 1)) :
    lapL ((stringVec (tripleF ℓ j) (highestVec ℓ j) (2 * ℓ) i : HomogP ℓ) : CoeffP) = 0 := by
  suffices h : ∀ m : ℕ, lapL (((tripleF ℓ j ^ m) (highestVec ℓ j) : HomogP ℓ) : CoeffP) = 0 from h i
  intro m
  induction m with
  | zero => exact lapL_isotropicForm_pow j ℓ
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, tripleF_coe, map_add, map_neg, map_smul, lapL_liftA, lapL_liftB, ih, map_zero,
      map_zero, neg_zero, smul_zero, add_zero]

private lemma planeEnd_of_zero (c : Fin 3) (w : HomogP 0) : planeEnd 0 c w = 0 := by
  refine Subtype.ext ?_
  have hw : (w : CoeffP) = C ((w : CoeffP).coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (w.2 : (w : CoeffP).IsHomogeneous 0).totalDegree_le)
  rw [planeEnd, restrictDeg_coe, Submodule.coe_zero, hw, planeDeriv, rotDeriv_C]

private lemma polySide :
    Function.Injective (polyString ℓ j) ∧
      (∀ (c : Fin 3) (a), polyString ℓ j (coordPlane (2 * ℓ) j c a) = planeEnd ℓ c (polyString ℓ j a)) ∧
      axisRot j (polyString ℓ j (Pi.single (zonalIndex ℓ) 1) : CoeffP) = 0 ∧
      lapL (polyString ℓ j (Pi.single (zonalIndex ℓ) 1) : CoeffP) = 0 := by
  have hharm : lapL (polyString ℓ j (Pi.single (zonalIndex ℓ) 1) : CoeffP) = 0 := by
    rw [polyString, stringMap_single]
    exact lapL_stringVec ℓ j _
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  · subst hℓ
    refine ⟨?_, fun c a => ?_, ?_, hharm⟩
    · intro a b hab
      rw [polyString, stringMap_apply_of_eq_zero _ _ rfl, stringMap_apply_of_eq_zero _ _ rfl] at hab
      funext i
      have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      rw [hi]
      exact smul_left_injective ℂ (highestVec_ne_zero 0 j) hab
    · rw [coordPlane_zero, LinearMap.zero_apply, map_zero, planeEnd_of_zero]
    · rw [polyString, stringMap_single]
      simp [stringVec, highestVec, axisRot]
  · have hprim := hasPrimitiveVector_axis ℓ hℓ j
    refine ⟨stringMap_injective hprim, ?_, ?_, hharm⟩
    · exact intertwine_coordPlane (R := axisRotEnd ℓ j) (A := liftAEnd ℓ j) (B := liftBEnd ℓ j) (planeEnd ℓ) j
        (planeEnd_eq_table ℓ j) (polyString ℓ j) (stringMap_coordH hprim) (stringMap_coordE hprim)
        (stringMap_coordF hprim)
    · have hw := h_stringVec hprim (zonalIndex ℓ)
      rw [← stringMap_single] at hw
      have hcoef : ((2 * ℓ : ℕ) : ℂ) - 2 * ((zonalIndex ℓ : ℕ) : ℂ) = 0 := by
        simp only [zonalIndex, Fin.val_mk]
        push_cast
        ring
      rw [hcoef, zero_smul, tripleH, LinearMap.smul_apply, smul_eq_zero] at hw
      rcases hw with h2 | hw
      · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      · have := congrArg Subtype.val hw
        rwa [axisRotEnd, restrictDeg_coe, Submodule.coe_zero] at this

end polynomialSide
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private lemma exists_eigenvector_of_involution {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ v, T (T v) = v) {z : M} (hz : z ≠ 0) :
    ∃ (ε : ℂ) (w : M), (ε = 1 ∨ ε = -1) ∧ w ≠ 0 ∧ T w = ε • w ∧ (w = z + T z ∨ w = z - T z) := by
  by_cases h : z + T z = 0
  · refine ⟨-1, z - T z, Or.inr rfl, ?_, ?_, Or.inr rfl⟩
    · have hTz : T z = -z := eq_neg_of_add_eq_zero_right h
      rw [hTz, sub_neg_eq_add, ← two_smul ℂ z]
      exact smul_ne_zero two_ne_zero hz
    · rw [map_sub, hT, neg_smul, one_smul, neg_sub]
  · exact ⟨1, z + T z, Or.inl rfl, h, by rw [map_add, hT, one_smul, add_comm], Or.inl rfl⟩

private lemma apply_eq_smul_of_commute {M : Type*} [AddCommGroup M] [Module ℂ M] {T X : Module.End ℂ M}
    (hc : Commute T X) {w : M} {ε : ℂ} (hw : T w = ε • w) : T (X w) = ε • X w := by
  have h := LinearMap.congr_fun hc w
  rw [Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h, hw, map_smul]

section groupSide

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (L : Fin 3 → Module.End ℂ E)
variable (htie :
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0))
variable (hrel :
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r))
variable (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E)

private def barR (j : Fin 3) : Module.End ℂ (E ⧸ groupKernel E) :=
  ![descendedOp E L htie 2, descendedOp E L htie 1, descendedOp E L htie 0] j
private def barA (j : Fin 3) : Module.End ℂ (E ⧸ groupKernel E) :=
  ![- descendedOp E L htie 0, descendedOp E L htie 0, descendedOp E L htie 1] j
private def barB (j : Fin 3) : Module.End ℂ (E ⧸ groupKernel E) :=
  ![- descendedOp E L htie 1, - descendedOp E L htie 2, descendedOp E L htie 2] j

private lemma barR_eq (j : Fin 3) : barR E L htie j = descendedOp E L htie (![2, 1, 0] j) := by
  fin_cases j <;> rfl

private lemma descendedOp_eq_table (j c : Fin 3) :
    descendedOp E L htie c = axisSign j c • ![barR E L htie j, barA E L htie j, barB E L htie j] (axisKind j c) := by
  fin_cases j <;> fin_cases c <;> simp [axisSign, axisKind, barR, barA, barB]

include hrel in
private lemma barA_barB_comm (j : Fin 3) (v : E ⧸ groupKernel E) :
    barA E L htie j (barB E L htie j v) - barB E L htie j (barA E L htie j v) = barR E L htie j v := by
  have h1 := descendedOp_comm_01 E L htie hrel v
  have h2 := descendedOp_comm_02 E L htie hrel v
  have h3 := descendedOp_comm_12 E L htie hrel v
  fin_cases j <;> simp only [barA, barB, barR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.neg_apply, map_neg, neg_neg]
  · linear_combination (norm := module) h1
  · linear_combination (norm := module) (-1 : ℂ) • h2
  · linear_combination (norm := module) h3

include hrel in
private lemma barR_barA_comm (j : Fin 3) (v : E ⧸ groupKernel E) :
    barR E L htie j (barA E L htie j v) - barA E L htie j (barR E L htie j v) = barB E L htie j v := by
  have h1 := descendedOp_comm_01 E L htie hrel v
  have h2 := descendedOp_comm_02 E L htie hrel v
  fin_cases j <;> simp only [barA, barB, barR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.neg_apply, map_neg]
  · linear_combination (norm := module) h2
  · linear_combination (norm := module) (-1 : ℂ) • h1
  · linear_combination (norm := module) h1

include hrel in
private lemma barR_barB_comm (j : Fin 3) (v : E ⧸ groupKernel E) :
    barR E L htie j (barB E L htie j v) - barB E L htie j (barR E L htie j v) = - barA E L htie j v := by
  have h2 := descendedOp_comm_02 E L htie hrel v
  have h3 := descendedOp_comm_12 E L htie hrel v
  fin_cases j <;> simp only [barA, barB, barR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.neg_apply, map_neg, neg_neg]
  · linear_combination (norm := module) h3
  · linear_combination (norm := module) (-1 : ℂ) • h3
  · linear_combination (norm := module) h2

private lemma descendedNeg_commute_descendedOp (c : Fin 3) :
    Commute (descendedNeg E hstab) (descendedOp E L htie c) :=
  LinearMap.ext (fun v => descendedNeg_comm_descendedOp E hstab L htie c v)

private lemma descendedNeg_commute_bars (j : Fin 3) :
    Commute (descendedNeg E hstab) (barR E L htie j) ∧ Commute (descendedNeg E hstab) (barA E L htie j) ∧
      Commute (descendedNeg E hstab) (barB E L htie j) := by
  have hc := descendedNeg_commute_descendedOp E L htie hstab
  fin_cases j <;> simp only [barR, barA, barB, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · exact ⟨hc 2, (hc 0).neg_right, (hc 1).neg_right⟩
  · exact ⟨hc 1, hc 0, (hc 2).neg_right⟩
  · exact ⟨hc 0, hc 1, hc 2⟩

include hrel in

private lemma groupSide [FiniteDimensional ℂ E] (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0)
    (j : Fin 3) :
    ∃ (ℓ : ℕ) (ε : ℂ) (Φ : (Fin (2 * ℓ + 1) → ℂ) →ₗ[ℂ] (E ⧸ groupKernel E)),
      (ε = 1 ∨ ε = -1) ∧
      (∀ (c : Fin 3) (a : Fin (2 * ℓ + 1) → ℂ), Φ (coordPlane (2 * ℓ) j c a) = descendedOp E L htie c (Φ a)) ∧
      (∀ a : Fin (2 * ℓ + 1) → ℂ, descendedNeg E hstab (Φ a) = ε • Φ a) ∧
      Φ (Pi.single (zonalIndex ℓ) 1) ≠ 0 := by
  haveI : Nontrivial (E ⧸ groupKernel E) := groupQuotient_nontrivial E hne
  set T := descendedNeg E hstab with hTdef
  have hTT : ∀ v, T (T v) = v := descendedNeg_descendedNeg E hstab
  obtain ⟨hcR, hcA, hcB⟩ := descendedNeg_commute_bars E L htie hstab j
  have hAB := barA_barB_comm E L htie hrel j
  have hRA := barR_barA_comm E L htie hrel j
  have hRB := barR_barB_comm E L htie hrel j
  by_cases hR : axisH (barR E L htie j) = 0
  ·
    have hR0 : barR E L htie j = 0 := by
      rcases smul_eq_zero.mp hR with h2 | h
      · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      · exact h
    have hB0 : barB E L htie j = 0 := LinearMap.ext (fun v => by
      have h := hRA v
      rwa [hR0, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero, eq_comm] at h)
    have hA0 : barA E L htie j = 0 := LinearMap.ext (fun v => by
      have h := hRB v
      rw [hR0, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, sub_zero, eq_comm, neg_eq_zero] at h
      exact h)
    have hL0 : ∀ c, descendedOp E L htie c = 0 := by
      intro c
      rw [descendedOp_eq_table E L htie j c, hR0, hA0, hB0]
      generalize axisKind j c = t
      fin_cases t <;> simp
    obtain ⟨z, hz⟩ := exists_ne (0 : E ⧸ groupKernel E)
    obtain ⟨ε, w, hε, hw0, hTw, -⟩ := exists_eigenvector_of_involution T hTT hz
    refine ⟨0, ε, stringMap 0 w 0, hε, ?_, ?_, ?_⟩
    · intro c a
      have h0 : coordPlane (2 * 0) j c = 0 := coordPlane_zero j c
      rw [h0, LinearMap.zero_apply, map_zero, hL0, LinearMap.zero_apply]
    · intro a
      rw [stringMap_apply_of_eq_zero _ _ rfl, map_smul, hTw, smul_comm]
    · rw [stringMap_single]
      simpa [stringVec] using hw0
  ·
    have t := isSl2Triple_axisTriple (barR E L htie j) (barA E L htie j) (barB E L htie j) hAB hRA hRB hR
    have hpv : ∃ (μ : ℂ) (z : E ⧸ groupKernel E), z ≠ 0 ∧ t.HasPrimitiveVectorWith z μ :=
      t.exists_hasPrimitiveVectorWith (R := ℂ) (M := E ⧸ groupKernel E)
    obtain ⟨μ, z, hz0, hz⟩ := hpv
    obtain ⟨n, rfl⟩ := hz.exists_nat

    have hRz : barR E L htie j z = ((-Complex.I / 2) * (n : ℂ)) • z := by
      have h := hz.lie_h
      change axisH (barR E L htie j) z = (n : ℂ) • z at h
      rw [axisH, LinearMap.smul_apply] at h
      have h' := congrArg (fun v => (-Complex.I / 2 : ℂ) • v) h
      simp only [smul_smul] at h'
      have hc : -Complex.I / 2 * (2 * Complex.I) = 1 := by linear_combination (-1 : ℂ) * Complex.I_mul_I
      rwa [hc, one_smul] at h'
    obtain ⟨m, hm⟩ := eigenvalue_descendedOp_eq_int_mul_I E L htie (![2, 1, 0] j) _ z hz0
      (by rw [← barR_eq]; exact hRz)
    have hn : ((n : ℕ) : ℤ) = -2 * m := by
      have h2 : ((n : ℕ) : ℂ) = -2 * (m : ℂ) := by
        linear_combination (2 * Complex.I) * hm + (((n : ℕ) : ℂ) + 2 * (m : ℂ)) * Complex.I_mul_I
      exact_mod_cast h2
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : ℕ, n = 2 * ℓ := ⟨n / 2, by omega⟩

    obtain ⟨ε, w, hε, hw0, hTw, hw⟩ := exists_eigenvector_of_involution T hTT hz0
    have hcH : Commute T (axisH (barR E L htie j)) := hcR.smul_right _
    have hcE : Commute T (axisE (barA E L htie j) (barB E L htie j)) := hcA.add_right (hcB.smul_right _)
    have hcF : Commute T (axisF (barA E L htie j) (barB E L htie j)) := hcA.neg_right.add_right (hcB.smul_right _)
    have hzh : axisH (barR E L htie j) z = ((2 * ℓ : ℕ) : ℂ) • z := hz.lie_h
    have hze : axisE (barA E L htie j) (barB E L htie j) z = 0 := hz.lie_e
    have hTzh : axisH (barR E L htie j) (T z) = ((2 * ℓ : ℕ) : ℂ) • T z := by
      have h := LinearMap.congr_fun hcH z
      rw [Module.End.mul_apply, Module.End.mul_apply, hzh, map_smul] at h
      exact h.symm
    have hTze : axisE (barA E L htie j) (barB E L htie j) (T z) = 0 := by
      have h := LinearMap.congr_fun hcE z
      rw [Module.End.mul_apply, Module.End.mul_apply, hze, map_zero] at h
      exact h.symm
    have hw_prim : t.HasPrimitiveVectorWith w ((2 * ℓ : ℕ) : ℂ) := by
      refine ⟨hw0, ?_, ?_⟩
      · change axisH (barR E L htie j) w = _
        rcases hw with rfl | rfl
        · rw [map_add, hzh, hTzh, smul_add]
        · rw [map_sub, hzh, hTzh, smul_sub]
      · change axisE (barA E L htie j) (barB E L htie j) w = 0
        rcases hw with rfl | rfl
        · rw [map_add, hze, hTze, add_zero]
        · rw [map_sub, hze, hTze, sub_zero]
    refine ⟨ℓ, ε, stringMap (axisF (barA E L htie j) (barB E L htie j)) w (2 * ℓ), hε, ?_, ?_, ?_⟩
    · exact intertwine_coordPlane (descendedOp E L htie) j (descendedOp_eq_table E L htie j) _
        (stringMap_coordH hw_prim) (stringMap_coordE hw_prim) (stringMap_coordF hw_prim)
    · intro a
      rw [stringMap_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, stringVec, apply_eq_smul_of_commute (hcF.pow_right _) hTw, smul_comm]
    · rw [stringMap_single]
      have hne := hw_prim.pow_toEnd_f_ne_zero_of_eq_nat (i := ℓ) rfl (by omega)
      rw [toEnd_end_eq] at hne
      exact hne

end groupSide
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private def substEnd (ℓ : ℕ) (k : Matrix (Fin 3) (Fin 3) ℝ) : Module.End ℂ (HomogP ℓ) :=
  (matrixSubst k).toLinearMap.restrict (fun _ hq => matrixSubst_isHomogeneous k hq)

private lemma substEnd_coe (ℓ : ℕ) (k : Matrix (Fin 3) (Fin 3) ℝ) (w : HomogP ℓ) :
    (substEnd ℓ k w : CoeffP) = matrixSubst k w :=
  rfl

private lemma substEnd_mul (ℓ : ℕ) (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    substEnd ℓ (x * y) = (substEnd ℓ x).comp (substEnd ℓ y) := by
  refine LinearMap.ext (fun w => Subtype.ext ?_)
  rw [LinearMap.comp_apply, substEnd_coe, substEnd_coe, substEnd_coe, matrixSubst_mul, AlgHom.comp_apply]

private lemma substEnd_one (ℓ : ℕ) : substEnd ℓ 1 = LinearMap.id := by
  refine LinearMap.ext (fun w => Subtype.ext ?_)
  rw [substEnd_coe, matrixSubst_one, AlgHom.id_apply, LinearMap.id_apply]

private lemma substEnd_neg_one (ℓ : ℕ) (w : HomogP ℓ) : substEnd ℓ (-1) w = ((-1 : ℂ) ^ ℓ) • w := by
  refine Subtype.ext ?_
  rw [substEnd_coe, Submodule.coe_smul, matrixSubst_neg_one w.2, smul_eq_C_mul, map_pow, C_neg, C_1]

private lemma det_neg_one_matrix : (((-1 : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) = -1 := by
  rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
  norm_num

private lemma exists_twist_exponent (ℓ : ℕ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    ∃ α : Fin 2, (-1 : ℂ) ^ (α : ℕ) * (-1) ^ ℓ = ε := by
  rcases neg_one_pow_eq_or ℂ ℓ with h | h <;> rcases hε with rfl | rfl
  · exact ⟨0, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩
  · exact ⟨0, by rw [h]; norm_num⟩

section stringEmbedding

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) (L : Fin 3 → Module.End ℂ E)
variable (htie :
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0))
variable (hrel :
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r))
variable (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E)

include hrel hstab in

private lemma exists_string_embedding [FiniteDimensional ℂ E]
    (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0) (j : Fin 3) :
    ∃ (ℓ : ℕ) (α : Fin 2) (S' : Submodule ℂ (HomogP ℓ)) (ι : S' →ₗ[ℂ] (E ⧸ groupKernel E))
      (hS : ∀ c : Fin 3, ∀ z ∈ S', planeEnd ℓ c z ∈ S'),
      (∀ (c : Fin 3) (z : S'), descendedOp E L htie c (ι z) = ι ((planeEnd ℓ c).restrict (hS c) z)) ∧
      Claim (substEnd ℓ) (groupEval E) S' ι (α : ℕ) negOneG ∧
      ∃ w₀ : S', axisRot j ((w₀ : HomogP ℓ) : CoeffP) = 0 ∧ lapL ((w₀ : HomogP ℓ) : CoeffP) = 0 ∧ ι w₀ ≠ 0 := by
  obtain ⟨ℓ, ε, Φ, hε, hΦ, hΦT, hΦ0⟩ := groupSide E L htie hrel hstab hne j
  obtain ⟨hinj, hP, hrot, hharm⟩ := polySide ℓ j
  obtain ⟨α, hα⟩ := exists_twist_exponent ℓ hε
  set ΦP := polyString ℓ j with hΦP
  let e : (Fin (2 * ℓ + 1) → ℂ) ≃ₗ[ℂ] LinearMap.range ΦP := LinearEquiv.ofInjective ΦP hinj
  have he : ∀ a, ((e a : LinearMap.range ΦP) : HomogP ℓ) = ΦP a := fun _ => rfl

  have hmem : ∀ z : LinearMap.range ΦP, ∃ a, e a = z := fun z => e.surjective z

  have hS : ∀ c : Fin 3, ∀ z ∈ LinearMap.range ΦP, planeEnd ℓ c z ∈ LinearMap.range ΦP := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨coordPlane (2 * ℓ) j c a, hP c a⟩
  refine ⟨ℓ, α, LinearMap.range ΦP, Φ ∘ₗ e.symm.toLinearMap, hS, ?_, ?_, e (Pi.single (zonalIndex ℓ) 1), ?_, ?_, ?_⟩
  ·
    intro c z
    obtain ⟨a, rfl⟩ := hmem z
    have h2 : (planeEnd ℓ c).restrict (hS c) (e a) = e (coordPlane (2 * ℓ) j c a) := by
      refine Subtype.ext ?_
      change planeEnd ℓ c (e a : HomogP ℓ) = (e (coordPlane (2 * ℓ) j c a) : HomogP ℓ)
      rw [he, he, hP]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2, e.symm_apply_apply, hΦ]
  ·
    intro z
    obtain ⟨a, rfl⟩ := hmem z
    refine ⟨ε • e a, ?_, ?_⟩
    · have hneg1 : ((negOneG : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = -1 := rfl
      rw [twisted_apply, hneg1, det_neg_one_matrix, Submodule.coe_smul, substEnd_neg_one, smul_smul, hα]
    · intro g
      rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← groupEval_descendedNeg E hstab]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, hΦT, map_smul, Pi.smul_apply,
        smul_eq_mul]
  · rw [he]
    exact hrot
  · rw [he]
    exact hharm
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
    exact hΦ0

end stringEmbedding
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

section conclusion

variable (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ))

private def extendByComponent (ℓ : ℕ) (lam : Module.Dual ℂ (HomogP ℓ)) : CoeffP →ₗ[ℂ] ℂ :=
  lam ∘ₗ (homogeneousComponent ℓ).codRestrict (homogeneousSubmodule (Fin 3) ℂ ℓ)
    (fun q => (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous (n := ℓ) (φ := q)))

private lemma extendByComponent_coe (ℓ : ℕ) (lam : Module.Dual ℂ (HomogP ℓ)) (w : HomogP ℓ) :
    extendByComponent ℓ lam w = lam w := by
  rw [extendByComponent, LinearMap.comp_apply]
  congr 1
  refine Subtype.ext ?_
  rw [LinearMap.codRestrict_apply, homogeneousComponent_of_mem w.2, if_pos rfl]

private lemma exists_polynomial_of_identification (j : Fin 3) (ℓ : ℕ) (α : Fin 2) (S' : Submodule ℂ (HomogP ℓ))
    (ι : S' →ₗ[ℂ] (E ⧸ groupKernel E)) (w₀ : S') (hrot : axisRot j ((w₀ : HomogP ℓ) : CoeffP) = 0)
    (hharm : lapL ((w₀ : HomogP ℓ) : CoeffP) = 0) (hι0 : ι w₀ ≠ 0)
    (hident : ∀ lam : Module.Dual ℂ (HomogP ℓ), (∀ z : S', lam z = groupEval E (ι z) 1) →
      ∀ (k : Matrix.orthogonalGroup (Fin 3) ℝ) (z : S'),
        groupEval E (ι z) k = (((k : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) ^ (α : ℕ) *
          lam (substEnd ℓ (k : Matrix (Fin 3) (Fin 3) ℝ) z)) :
    ∃ (α : Fin 2) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ F ∈ E, ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        F r = ((r.det : ℝ) : ℂ) ^ (α : ℕ) *
          MvPolynomial.eval (fun ab : Fin 3 × Fin 3 => ((r ab.1 ab.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by

  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend ((evalPoint 1) ∘ₗ (groupEval E) ∘ₗ ι)
  have hlam' : ∀ z : S', lam z = groupEval E (ι z) 1 := fun z => by
    have h := LinearMap.congr_fun hlam z
    simpa [evalPoint] using h
  have hid := hident lam hlam'

  obtain ⟨κ, s, c, m, n, hmn, hq⟩ :=
    exists_axisSubst_of_rotDeriv_eq_zero j (w₀ : HomogP ℓ).2 (by simpa [axisRot] using hrot)
  set Ψ : MvPolynomial (Fin 2) ℂ := ∑ e ∈ s, C (c e) * X 0 ^ m e * X 1 ^ n e with hΨ
  set Λ := extendByComponent ℓ lam with hΛ
  set p : CoeffP := applyCoeff Λ (pairSubst Ψ) with hp

  have hident' : ∀ k : Matrix.orthogonalGroup (Fin 3) ℝ,
      groupEval E (ι w₀) k = (((k : Matrix (Fin 3) (Fin 3) ℝ).det : ℝ) : ℂ) ^ (α : ℕ) *
        eval (fun i => (((k : Matrix (Fin 3) (Fin 3) ℝ) i j : ℝ) : ℂ)) p := by
    intro k
    have hk1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp k.2
    have hk2 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp k.2
    rw [hid k w₀, hp, eval_applyCoeff_column, ← matrixSubst_axisSubst _ hk1 hk2, ← hq, hΛ, ← substEnd_coe,
      extendByComponent_coe]
  refine ⟨α, ℓ, p, ?_, applyCoeff_isHomogeneous Λ (pairSubst_sum_isHomogeneous s c m n hmn), ?_, ?_⟩
  ·
    intro hp0
    apply hι0
    apply groupEval_injective E
    funext k
    rw [map_zero, Pi.zero_apply, hident' k, hp0, map_zero, mul_zero]
  · rw [← lapL_apply, hp, lapL_applyCoeff, lapL_pairSubst_eq_zero j Ψ (by rw [← hq]; exact hharm), applyCoeff_zero]
  · obtain ⟨F, hF, hFeq⟩ := exists_mem_eq_groupEval E (ι w₀)
    refine ⟨F, hF, fun r hr => ?_⟩
    rw [hFeq r hr, hident' ⟨r, hr⟩, eval_column_realisation]

end conclusion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

end AxisHarmonics
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable.AxisHarmonics"

private noncomputable def evalLin (y : Fin 3 → ℂ) : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] ℂ where
  toFun := MvPolynomial.eval y
  map_add' p q := map_add _ p q
  map_smul' b p := by simp [MvPolynomial.smul_eval]

private theorem evalLin_apply (y : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) : evalLin y p = MvPolynomial.eval y p :=
  rfl

private noncomputable def evalFamily (W : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) : Set (Module.Dual ℂ W) :=
  Set.range fun y : Fin 3 → ℂ => (evalLin y).comp W.subtype

private theorem evalFamily_separating (W : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) (w : W)
    (h : ∀ φ ∈ evalFamily W, φ w = 0) : w = 0 := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro y
  rw [Submodule.coe_zero, map_zero]
  exact h _ ⟨y, rfl⟩

private theorem evalFamily_flow (ℓ : ℕ) (φ : Module.Dual ℂ (AxisHarmonics.HomogP ℓ))
    (hφ : φ ∈ evalFamily (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ)) (c : Fin 3) (w : AxisHarmonics.HomogP ℓ)
    (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => φ (AxisHarmonics.substEnd ℓ (rot (planes c).1 (planes c).2 s) w))
      (φ (AxisHarmonics.substEnd ℓ (rot (planes c).1 (planes c).2 s₀) (AxisHarmonics.planeEnd ℓ c w))) s₀ := by
  obtain ⟨y, rfl⟩ := hφ
  fin_cases c
  · exact hasDerivAt_eval_matrixSubst_planeRotation01 w y s₀
  · exact hasDerivAt_eval_matrixSubst_planeRotation02 w y s₀
  · exact hasDerivAt_eval_matrixSubst_planeRotation12 w y s₀

private theorem rot_eq_statement_literal :
    rot = fun c₁ c₂ s => Matrix.of fun i k =>
      if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
      if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
      if i = k then (1 : ℝ) else 0
    := rfl

theorem solution
    (j : Fin 3) (E : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℝ → ℂ)) [FiniteDimensional ℂ E]
    (hne : ∃ F ∈ E, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0)
    (hstab : ∀ F ∈ E, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ, (fun r => F (r * r₀)) ∈ E) :
    let rot : Fin 3 → Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun c₁ c₂ s => Matrix.of fun i k =>
      if i = c₁ ∧ k = c₁ then Real.cos s else if i = c₂ ∧ k = c₂ then Real.cos s else
      if i = c₁ ∧ k = c₂ then - Real.sin s else if i = c₂ ∧ k = c₁ then Real.sin s else
      if i = k then (1 : ℝ) else 0
    let planes : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]
    let val : E → Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun F => (F : Matrix (Fin 3) (Fin 3) ℝ → ℂ)
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    ∀ L : Fin 3 → Module.End ℂ E,
      (∀ (F : E) (c : Fin 3), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        HasDerivAt (fun s : ℝ => val F (r * rot (planes c).1 (planes c).2 s)) (val (L c F) r) 0) →
      (∀ (F : E), ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        val (L 0 (L 1 F)) r - val (L 1 (L 0 F)) r = val (L 2 F) r ∧
        val (L 0 (L 2 F)) r - val (L 2 (L 0 F)) r = - val (L 1 F) r ∧
        val (L 1 (L 2 F)) r - val (L 2 (L 1 F)) r = val (L 0 F) r) →
      ∃ (α : Fin 2) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ F ∈ E, ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
        F r = ((r.det : ℝ) : ℂ) ^ (α : ℕ) *
          MvPolynomial.eval (fun ab : Fin 3 × Fin 3 => ((r ab.1 ab.2 : ℝ) : ℂ)) (realise p) := by
  intro rot planes val realise L htie hrel
  obtain ⟨ℓ, α, S', ι, hS, hι, hneg, w₀, hrot, hharm, hι0⟩ :=
    AxisHarmonics.exists_string_embedding E L htie hrel hstab hne j
  exact AxisHarmonics.exists_polynomial_of_identification E j ℓ α S' ι w₀ hrot hharm hι0 fun lam hlam k z =>
    eval_eq_twisted (AxisHarmonics.substEnd ℓ) (AxisHarmonics.planeEnd ℓ) (groupEval E) (descendedOp E L htie) S' ι
      (α : ℕ) (AxisHarmonics.substEnd_mul ℓ) hS (AxisHarmonics.substEnd_one ℓ)
      (evalFamily (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ))
      (evalFamily_separating (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ)) (evalFamily_flow ℓ)
      (hasDerivAt_groupEval_flowPoint E L htie) hι hneg lam hlam k z

end S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable (solution)
