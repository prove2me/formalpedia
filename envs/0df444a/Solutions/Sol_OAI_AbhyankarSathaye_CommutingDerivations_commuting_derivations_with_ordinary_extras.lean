-- Prove2me | solution 1 for OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:02:48.122384+00:00
-- url     : https://prove2.me/submissions/1a4a73f6-60cf-4283-a29e-3e32e7483fe1

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/OrdinaryExtraMain.lean:L25-L85
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_commuting_derivations_with_ordinary_extras) verbatim and is proved by it.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizedPartials
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_OrdinaryExtraMain
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coordinate_partial_iterate_eq_zero
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coordinate_partials_common_kernel
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_descended_linearIndependent
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_exists_common_denominator_descent
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_extended_isLocalization
import Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_extended_localization_kernel_intersection

-- ---- from OAI.AlgebraicGeometry.AbhyankarSathaye.Identities ----
namespace OAI

/-!
# Polynomial identities for the cusp and the explicit hypersurface

The polynomials `S` and `P` give the identity
`(x + s³)² + (y - s²)³ = s * (1 + F)`. The Bézout certificate is valid over
every commutative ring. In the ambient complex polynomial ring, the variables
are ordered as `h, u, v, w`.
-/

noncomputable section
namespace AbhyankarSathaye

theorem shift : shiftX^2 + shiftY^3 = x^2 + y^3 - s*p :=
  shift_universal x y s

theorem ambient : shiftX^2 + shiftY^3 = s*(1 + F) := by
  rw [shift, cusp]
  unfold F
  ring

end AbhyankarSathaye

end

end OAI

-- ---- from OAI.AlgebraicGeometry.AbhyankarSathaye.CriticalPoint ----
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

end AbhyankarSathaye

end

end OAI

-- ---- from OAI.AlgebraicGeometry.AbhyankarSathaye.NonCoordinate ----
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

end AbhyankarSathaye

end

end OAI

-- ---- from OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization ----
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

end AbhyankarSathaye

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization ----
namespace OAI

/-!
Localization coordinates in every dimension `n ≥ 4`.

The localization at `extendedF hn + 1` is a polynomial extension of the
four-dimensional localization, with an explicit structural map from the ambient ring.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem extendedScalarTower {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) (ExtendedLocalizedAmbient n) :=
  IsScalarTower.of_algHom (extendedLocAlgHom hn)

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedParameterRetraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The explicit intersection proof retains every dimension n >= 4 and
identifies its ordinary polynomial side with the standard subalgebra C[F_n]. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

theorem extendedParameter_ne_zero {n : ℕ} (hn : 4 ≤ n) : extendedAmbientParameter hn ≠ 0 := by
  intro hh
  have he := congrArg (extendedParameterSlice hn) hh
  simp at he

theorem extendedParameter_localization_injective {n : ℕ} (hn : 4 ≤ n)
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin n) ℂ) L]
    [IsLocalization.Away (extendedAmbientParameter hn) L] :
    Function.Injective (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
  apply IsLocalization.injective L (M := Submonoid.powers (extendedAmbientParameter hn))
  intro z hz
  obtain ⟨m, rfl⟩ := hz
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m (extendedParameter_ne_zero hn))

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations ----
namespace OAI

/-!
Transport, scaling, and descent of derivations through algebra homomorphisms.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

theorem transportDerivation_iterate (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (n : ℕ) (a : A) :
    (transportDerivation e D : A → A)^[n] a = e.symm ((D : B → B)^[n] (e a)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', transportDerivation_apply,
      ih, e.apply_symm_apply]

theorem transportDerivation_locallyNilpotent (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (hD : LocallyNilpotent D) :
    LocallyNilpotent (transportDerivation e D) := by
  intro a
  obtain ⟨n, hn⟩ := hD (e a)
  exact ⟨n, by rw [transportDerivation_iterate, hn, map_zero]⟩

/-- Multiplication by a kernel element gives the exact nth-iterate formula. -/
theorem scaleDerivation_iterate (D : Derivation K A A) (c : A) (hc : D c = 0)
    (n : ℕ) (a : A) :
    ((c • D : Derivation K A A) : A → A)^[n] a = c^n * (D : A → A)^[n] a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.smul_apply]
      simp only [smul_eq_mul, Derivation.leibniz, Derivation.leibniz_pow, hc,
        smul_zero, mul_zero, add_zero, Function.iterate_succ_apply']
      rw [pow_succ]
      ring

theorem scaleDerivation_locallyNilpotent (D : Derivation K A A) (c : A)
    (hc : D c = 0) (hD : LocallyNilpotent D) : LocallyNilpotent (c • D) := by
  intro a
  obtain ⟨n, hn⟩ := hD a
  exact ⟨n, by rw [scaleDerivation_iterate D c hc, hn, mul_zero]⟩

/-- Different multipliers may be used if both lie in both kernels. -/
theorem scaleDerivation_commute (D E : Derivation K A A) (a b : A)
    (hDb : D b = 0) (hEa : E a = 0) (hDE : ∀ x, D (E x) = E (D x)) (x : A) :
    (a • D) ((b • E) x) = (b • E) ((a • D) x) := by
  simp only [Derivation.smul_apply, smul_eq_mul, Derivation.leibniz, hDb, hEa,
    mul_zero, add_zero, hDE]
  ring

theorem descendDerivation_iterate (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a))
    (n : ℕ) (a : A) :
    ι ((descendDerivation ι hι D d hd : A → A)^[n] a) =
      (D : B → B)^[n] (ι a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', descendDerivation_apply, hd, ih]

theorem descendDerivation_locallyNilpotent (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a))
    (hD : LocallyNilpotent D) : LocallyNilpotent (descendDerivation ι hι D d hd) := by
  intro a
  obtain ⟨n, hn⟩ := hD (ι a)
  refine ⟨n, hι ?_⟩
  rw [descendDerivation_iterate, hn, map_zero]

theorem descendDerivation_commute (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D E : Derivation K B B) (d e : A → A)
    (hd : ∀ a, ι (d a) = D (ι a)) (he : ∀ a, ι (e a) = E (ι a))
    (hDE : ∀ b, D (E b) = E (D b)) (a : A) :
    descendDerivation ι hι D d hd (descendDerivation ι hι E e he a) =
      descendDerivation ι hι E e he (descendDerivation ι hι D d hd a) := by
  apply hι
  simp only [descendDerivation_apply, hd, he, hDE]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.DescentFamily ----
namespace OAI

/-! Properties of an actual descended family with a common clearing power.
All hypotheses describe explicit maps and identities; none assumes the desired
family properties on the original ring. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

variable {K A L I : Type*} [CommRing K] [CommRing A] [CommRing L]
  [Algebra K A] [Algebra K L]

theorem descended_fixes_parameter (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a)) (hfix : D (ι c) = 0) :
    d c = 0 := by
  apply hinj
  simpa [hfix] using hdesc c

theorem descended_kernel (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (hu : IsUnit (ι c)) (N : ℕ)
    (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a)) (a : A) :
    d a = 0 ↔ D (ι a) = 0 := by
  constructor
  · intro hz
    have he := hdesc a
    rw [hz, map_zero] at he
    exact (hu.pow N).mul_right_eq_zero.mp he.symm
  · intro hz
    apply hinj
    simpa [hz] using hdesc a

theorem descended_locallyNilpotent (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D : Derivation K L L) (d : Derivation K A A)
    (hdesc : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (hfix : D (ι c) = 0) (hD : LocallyNilpotent D) : LocallyNilpotent d := by
  have hp : D ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hfix]
  exact descendDerivation_locallyNilpotent ι hinj ((ι c)^N • D) d
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hdesc)
    (scaleDerivation_locallyNilpotent D ((ι c)^N) hp hD)

theorem descended_commute (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N : ℕ) (D E : Derivation K L L) (d e : Derivation K A A)
    (hd : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (he : ∀ a, ι (e a) = (ι c)^N * E (ι a))
    (hD : D (ι c) = 0) (hE : E (ι c) = 0)
    (hDE : ∀ a, D (E a) = E (D a)) (a : A) : d (e a) = e (d a) := by
  have hDp : D ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hD]
  have hEp : E ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hE]
  exact descendDerivation_commute ι hinj ((ι c)^N • D) ((ι c)^N • E) d e
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hd)
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using he)
    (scaleDerivation_commute D E ((ι c)^N) ((ι c)^N) hDp hEp hDE) a

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.CoordinatePartials ----
namespace OAI

/-! The actual polynomial coordinate partials: commuting, locally nilpotent,
linearly independent over the polynomial ring, and with exact constant common
kernel in characteristic zero. No localization equivalence is assumed here. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {B σ : Type*} [CommRing B]

theorem coordinate_partials_commute (i j : σ) (p : MvPolynomial σ B) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp [coeff_pderiv, Finsupp.add_apply, hij, Ne.symm hij,
    add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc]

/-- An explicit pointwise bound: one more than the largest exponent of i
among the finitely many supported monomials. -/
theorem coordinate_partial_nilpotence_bound (i : σ) (p : MvPolynomial σ B) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[
      p.support.sup (fun m => m i) + 1] p = 0 := by
  classical
  apply coordinate_partial_iterate_eq_zero
  intro m hm
  by_contra hc
  have hmem : m ∈ p.support := mem_support_iff.mpr hc
  have hle : m i ≤ p.support.sup (fun a => a i) :=
    Finset.le_sup (f := fun a : σ →₀ ℕ => a i) hmem
  exact (Nat.not_succ_le_self _) (hm.trans hle)

theorem coordinate_partial_locallyNilpotent (i : σ) :
    LocallyNilpotent (pderiv i : Derivation B (MvPolynomial σ B) (MvPolynomial σ B)) := by
  intro p
  exact ⟨p.support.sup (fun m => m i) + 1, coordinate_partial_nilpotence_bound i p⟩

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.LocalizedPartials ----
namespace OAI

/-! Transport the actual coordinate partials through a specified, proved
algebra equivalence. Coefficients in the whole relative coefficient algebra
are fixed, even when the derivations are viewed over a smaller ground ring. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L I : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L]

theorem localizedPartial_locallyNilpotent (e : L ≃ₐ[K] MvPolynomial I B) (i : I) :
    LocallyNilpotent (localizedPartial e i) :=
  transportDerivation_locallyNilpotent e _ (coordinate_partial_locallyNilpotent i)

theorem localizedPartials_commute (e : L ≃ₐ[K] MvPolynomial I B) (i j : I) (a : L) :
    localizedPartial e i (localizedPartial e j a) =
      localizedPartial e j (localizedPartial e i a) := by
  simp only [localizedPartial_apply, e.apply_symm_apply, coordinate_partials_commute i j]

theorem localizedPartial_fixes_relative (e : L ≃ₐ[K] MvPolynomial I B)
    (i : I) (a : L) (b : B) (hab : e a = C b) : localizedPartial e i a = 0 := by
  rw [localizedPartial_apply, hab, pderiv_C, map_zero]

theorem localizedPartial_coordinate [DecidableEq I]
    (e : L ≃ₐ[K] MvPolynomial I B) (i j : I) :
    localizedPartial e i (e.symm (X j)) = if i = j then 1 else 0 := by
  simp [localizedPartial_apply, pderiv_X, Pi.single_apply, eq_comm]

theorem localizedPartial_kernel (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = 0 ↔ pderiv i (e a) = 0 := by
  constructor
  · intro h
    have hh := congrArg e h
    simpa only [localizedPartial_apply, e.apply_symm_apply, map_zero] using hh
  · intro h
    rw [localizedPartial_apply, h, map_zero]

theorem localizedPartials_common_kernel [IsDomain B] [CharZero B]
    (e : L ≃ₐ[K] MvPolynomial I B) (a : L) :
    (∀ i, localizedPartial e i a = 0) ↔ ∃ b : B, e a = C b := by
  simp only [localizedPartial_kernel]
  exact coordinate_partials_common_kernel (e a)

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.FamilyFromLocalization ----
namespace OAI

/-!
Construction of a commuting, locally nilpotent, linearly independent family
from a relative localization equivalence and a coefficient-intersection identity.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L σ τ : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L] [Algebra (MvPolynomial σ K) L]
  [IsScalarTower K (MvPolynomial σ K) L] [Fintype σ] [Fintype τ]
  [IsDomain B] [CharZero B]

theorem exists_commuting_family_of_localization
    (c : MvPolynomial σ K) [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (e : L ≃ₐ[K] MvPolynomial τ B) (b : B)
    (hec : e (algebraMap (MvPolynomial σ K) L c) = C b)
    (S : Subalgebra K (MvPolynomial σ K))
    (hintersection : ∀ p : MvPolynomial σ K,
      (∃ b : B, e (algebraMap (MvPolynomial σ K) L p) = C b) ↔ p ∈ S) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      (∀ i p, algebraMap (MvPolynomial σ K) L (d i p) =
        (algebraMap (MvPolynomial σ K) L c)^N *
          localizedPartial e i (algebraMap (MvPolynomial σ K) L p)) ∧
      (∀ i, d i c = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial σ K) d ∧
      (∀ p, (∀ i, d i p = 0) ↔ p ∈ S) := by
  classical
  let ι : MvPolynomial σ K →ₐ[K] L :=
    IsScalarTower.toAlgHom K (MvPolynomial σ K) L
  let D : τ → Derivation K L L := localizedPartial e
  have hfix (i : τ) : D i (ι c) = 0 :=
    localizedPartial_fixes_relative e i (ι c) b hec
  have hu : IsUnit (ι c) := IsLocalization.Away.algebraMap_isUnit c
  obtain ⟨N, d, hd⟩ := exists_common_denominator_descent c hinj D
  have hd' (i : τ) (p : MvPolynomial σ K) :
      ι (d i p) = (ι c)^N * D i (ι p) := hd i p
  refine ⟨N, d, hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact descended_fixes_parameter ι hinj c N (D i) (d i) (hd' i) (hfix i)
  · intro i j p
    exact descended_commute ι hinj c N (D i) (D j) (d i) (d j)
      (hd' i) (hd' j) (hfix i) (hfix j) (localizedPartials_commute e i j) p
  · intro i
    exact descended_locallyNilpotent ι hinj c N (D i) (d i) (hd' i) (hfix i)
      (localizedPartial_locallyNilpotent e i)
  · apply descended_linearIndependent ι hinj c hu N D d hd' hfix
      (fun j => e.symm (X j)) (localizedPartial_coordinate e)
    intro j
    exact IsLocalization.Away.surj c (e.symm (X j))
  · intro p
    calc
      (∀ i, d i p = 0) ↔ ∀ i, D i (ι p) = 0 :=
        forall_congr' (fun i => descended_kernel ι hinj c hu N (D i) (d i) (hd' i) p)
      _ ↔ ∃ b : B, e (ι p) = C b := localizedPartials_common_kernel e (ι p)
      _ ↔ p ∈ S := hintersection p

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.KernelObstruction ----
namespace OAI

/-! Every element of the proposed common kernel has a critical point.
This proves the coordinate obstruction for all such elements, independently
of whether they generate that subalgebra. It does not assert kernel equality. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem critical_aeval {σ B : Type*} [CommRing B]
    (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) (i : σ) :
    eval point (pderiv i (Polynomial.aeval f q)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, hq, hr, add_zero]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.aeval_C, MvPolynomial.algebraMap_eq, hc]

theorem no_coordinate_aeval_of_critical {σ B : Type*} [Fintype σ] [CommRing B]
    [Nontrivial B] (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) :
    ¬ ∃ (e : MvPolynomial σ B ≃ₐ[B] MvPolynomial σ B) (i : σ),
      e (X i) = Polynomial.aeval f q :=
  no_coordinate_of_critical _ point (critical_aeval f point hc q)

theorem polynomial_in_extendedF_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (q : Polynomial ℂ) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = Polynomial.aeval (extendedF hn) q :=
  no_coordinate_aeval_of_critical (extendedF hn) (extendedPoint hn)
    (extendedF_critical hn) q

/-- In particular, no generator of a common kernel equal to `C[F_n]` can
be a coordinate. The explicit polynomial-expression hypothesis suffices. -/
theorem element_of_extendedF_subring_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (g : MvPolynomial (Fin n) ℂ)
    (hg : ∃ q : Polynomial ℂ, g = Polynomial.aeval (extendedF hn) q) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = g := by
  obtain ⟨q, rfl⟩ := hg
  exact polynomial_in_extendedF_not_coordinate hn q

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.ExtendedExtraPartials ----
namespace OAI

/-!
Ordinary partial derivatives in the unused variables agree with the corresponding
localized coordinate derivatives and descend without a clearing factor.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem pderiv_sumAlgEquiv_symm {K I J : Type*} [CommRing K]
    (i : I) (p : MvPolynomial I (MvPolynomial J K)) :
    pderiv (Sum.inl i) ((sumAlgEquiv K I J).symm p) =
      (sumAlgEquiv K I J).symm (pderiv i p) := by
  apply (sumAlgEquiv K I J).injective
  simpa using (pderiv_sumAlgEquiv i ((sumAlgEquiv K I J).symm p)).symm

theorem splitAmbient_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    pderiv i (splitAmbient hn p) =
      splitAmbient hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  have he := pderiv_rename (blocksToAmbient hn).symm.injective
    (blocksToAmbient hn (Sum.inl i)) p
  simp only [Equiv.symm_apply_apply] at he
  change pderiv i
      (sumAlgEquiv ℂ (Fin (n-4)) (Fin 4) (rename (blocksToAmbient hn).symm p)) =
    sumAlgEquiv ℂ (Fin (n-4)) (Fin 4)
      (rename (blocksToAmbient hn).symm (pderiv (blocksToAmbient hn (Sum.inl i)) p))
  rw [pderiv_sumAlgEquiv, he]

theorem extendedLocMap_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    pderiv i (extendedLocMap hn p) =
      extendedLocMap hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  change pderiv i (MvPolynomial.map loc (splitAmbient hn p)) =
    MvPolynomial.map loc
      (splitAmbient hn (pderiv (blocksToAmbient hn (Sum.inl i)) p))
  rw [pderiv_map, splitAmbient_extra_pderiv]

theorem extendedLocalizationEquiv_extra_pderiv {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : ExtendedLocalizedAmbient n) :
    pderiv (blocksToOutput hn (Sum.inl i)) (extendedLocalizationEquiv hn p) =
      extendedLocalizationEquiv hn (pderiv i p) := by
  change pderiv (blocksToOutput hn (Sum.inl i))
      (rename (blocksToOutput hn)
        ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
          (MvPolynomial.map localizationComplexEquiv p))) =
    rename (blocksToOutput hn)
      ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
        (MvPolynomial.map localizationComplexEquiv (pderiv i p)))
  rw [pderiv_rename (blocksToOutput hn).injective, pderiv_sumAlgEquiv_symm, pderiv_map]

/-- The transported derivative indexed by an added coordinate agrees exactly
with the ordinary partial derivative in the full original n-variable ring. -/
theorem localized_extra_is_ordinary_partial {n : ℕ} (hn : 4 ≤ n)
    (i : Fin (n-4)) (p : MvPolynomial (Fin n) ℂ) :
    localizedPartial (extendedLocalizationEquiv hn) (blocksToOutput hn (Sum.inl i))
        (extendedLocMap hn p) =
      extendedLocMap hn (pderiv (blocksToAmbient hn (Sum.inl i)) p) := by
  apply (extendedLocalizationEquiv hn).injective
  rw [localizedPartial_apply, AlgEquiv.apply_symm_apply,
    extendedLocalizationEquiv_extra_pderiv, extendedLocMap_extra_pderiv]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.MixedDescentFamily ----
namespace OAI

/-! Each coordinate direction may use its own power of the fixed parameter.
In particular, additional ordinary coordinate partials use exponent zero. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K A B L I : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing L]
  [Algebra K A] [Algebra K B] [Algebra K L]

theorem mixed_descended_commute (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N M : ℕ) (D E : Derivation K L L) (d e : Derivation K A A)
    (hd : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (he : ∀ a, ι (e a) = (ι c)^M * E (ι a))
    (hD : D (ι c) = 0) (hE : E (ι c) = 0)
    (hDE : ∀ a, D (E a) = E (D a)) (a : A) : d (e a) = e (d a) := by
  have hDp : D ((ι c)^M) = 0 := by simp [Derivation.leibniz_pow, hD]
  have hEp : E ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hE]
  exact descendDerivation_commute ι hinj ((ι c)^N • D) ((ι c)^M • E) d e
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hd)
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using he)
    (scaleDerivation_commute D E ((ι c)^N) ((ι c)^M) hDp hEp hDE) a

theorem mixed_descended_linearIndependent [Fintype I] [DecidableEq I]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A)
    (hu : IsUnit (ι c)) (N : I → ℕ)
    (D : I → Derivation K L L) (d : I → Derivation K A A)
    (hdesc : ∀ i a, ι (d i a) = (ι c)^(N i) * D i (ι a))
    (hfix : ∀ i, D i (ι c) = 0)
    (t : I → L) (ht : ∀ i j, D i (t j) = if i = j then 1 else 0)
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), t j * (ι c)^n = ι r) :
    LinearIndependent A d := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  obtain ⟨n, r, hr⟩ := hfrac j
  have hir (i : I) : D i (ι r) = (ι c)^n * (if i = j then 1 else 0) := by
    rw [← hr, Derivation.leibniz]
    simp [Derivation.leibniz_pow, hfix, ht, smul_eq_mul]
  let ev : Derivation K A A →+ A :=
    { toFun := fun E => E r
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : ∑ i, a i * d i r = 0 := by
    have he' := congrArg ev ha
    rw [map_sum, map_zero] at he'
    simpa [ev, Derivation.smul_apply, smul_eq_mul] using he'
  have hj : (ι (a j) * (ι c)^(N j)) * (ι c)^n = 0 := by
    simpa [map_sum, hdesc, hir, mul_ite, ite_mul, mul_assoc] using congrArg ι he
  apply hinj
  rw [map_zero]
  exact (hu.pow (N j)).mul_left_eq_zero.mp ((hu.pow n).mul_left_eq_zero.mp hj)

theorem family_properties_of_mixed_descent [Fintype I] [IsDomain B] [CharZero B]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A) (hu : IsUnit (ι c))
    (e : L ≃ₐ[K] MvPolynomial I B) (b : B) (hc : e (ι c) = C b)
    (N : I → ℕ) (d : I → Derivation K A A)
    (hd : ∀ i a, ι (d i a) = (ι c)^(N i) * localizedPartial e i (ι a))
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), e.symm (X j) * (ι c)^n = ι r)
    (S : Subalgebra K A)
    (hintersection : ∀ a, (∃ b : B, e (ι a) = C b) ↔ a ∈ S) :
    (∀ i, d i c = 0) ∧
      (∀ i j a, d i (d j a) = d j (d i a)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧ LinearIndependent A d ∧
      (∀ a, (∀ i, d i a = 0) ↔ a ∈ S) := by
  classical
  have hfix (i : I) : localizedPartial e i (ι c) = 0 :=
    localizedPartial_fixes_relative e i (ι c) b hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact descended_fixes_parameter ι hinj c (N i) _ _ (hd i) (hfix i)
  · intro i j a
    exact mixed_descended_commute ι hinj c (N i) (N j) _ _ _ _
      (hd i) (hd j) (hfix i) (hfix j) (localizedPartials_commute e i j) a
  · intro i
    exact descended_locallyNilpotent ι hinj c (N i) _ _ (hd i) (hfix i)
      (localizedPartial_locallyNilpotent e i)
  · exact mixed_descended_linearIndependent ι hinj c hu N _ d hd hfix
      (fun j => e.symm (X j)) (localizedPartial_coordinate e) hfrac
  · intro a
    calc
      (∀ i, d i a = 0) ↔ ∀ i, localizedPartial e i (ι a) = 0 :=
        forall_congr' (fun i => descended_kernel ι hinj c hu (N i) _ _ (hd i) a)
      _ ↔ ∃ b : B, e (ι a) = C b := localizedPartials_common_kernel e (ι a)
      _ ↔ a ∈ S := hintersection a

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- from OAI.AlgebraicGeometry.CommutingDerivations.OrdinaryExtraMain ----
namespace OAI

/-! The all-dimensional family may be chosen with the additional n-4
directions literally equal to the ordinary ambient coordinate partials. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem commuting_derivations_with_ordinary_extras (n : ℕ) (hn : 4 ≤ n) :
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) ∧
      (∀ i : Fin (n-4), d (blocksToOutput hn (Sum.inl i)) =
        pderiv (blocksToAmbient hn (Sum.inl i))) := by
  let := extendedAlgebra hn
  let := extendedScalarTower hn
  let := extended_isLocalization hn
  let : IsLocalization.Away (extendedAmbientParameter hn) (ExtendedLocalizedAmbient n) := by
    change IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n)
    exact extended_isLocalization hn
  let ι : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ExtendedLocalizedAmbient n := extendedLocAlgHom hn
  have hinj : Function.Injective ι :=
    extendedParameter_localization_injective hn (ExtendedLocalizedAmbient n)
  have hu : IsUnit (ι (extendedF hn+1)) :=
    IsLocalization.Away.algebraMap_isUnit (extendedF hn+1)
  obtain ⟨N, d, hdesc, _, _, _, _, _⟩ :=
    exists_commuting_family_of_localization (extendedF hn + 1) hinj
      (extendedLocalizationEquiv hn) coefficientC (extendedLocalizationEquiv_c hn)
      (Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)))
      (extended_localization_kernel_intersection hn)
  have hdesc' (k : Fin (n-1)) (p : MvPolynomial (Fin n) ℂ) :
      ι (withOrdinaryExtras hn d k p) =
        (ι (extendedF hn+1))^(extraClearingExponent hn N k) *
          localizedPartial (extendedLocalizationEquiv hn) k (ι p) := by
    obtain ⟨j, rfl⟩ := (blocksToOutput hn).surjective k
    cases j with
    | inl i =>
        simp only [withOrdinaryExtras, extraClearingExponent,
          Equiv.symm_apply_apply, pow_zero, one_mul]
        exact (localized_extra_is_ordinary_partial hn i p).symm
    | inr j =>
        simp only [withOrdinaryExtras, extraClearingExponent,
          Equiv.symm_apply_apply]
        exact hdesc (blocksToOutput hn (Sum.inr j)) p
  have hfrac (j : Fin (n-1)) : ∃ (m : ℕ) (r : MvPolynomial (Fin n) ℂ),
      (extendedLocalizationEquiv hn).symm (X j) * (ι (extendedF hn+1))^m = ι r :=
    IsLocalization.Away.surj (extendedF hn+1) ((extendedLocalizationEquiv hn).symm (X j))
  obtain ⟨hfix, hcomm, hnil, hind, hker⟩ :=
    family_properties_of_mixed_descent ι hinj (extendedF hn+1) hu
      (extendedLocalizationEquiv hn) coefficientC (extendedLocalizationEquiv_c hn)
      (extraClearingExponent hn N) (withOrdinaryExtras hn d) hdesc' hfrac
      (Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)))
      (extended_localization_kernel_intersection hn)
  refine ⟨withOrdinaryExtras hn d, hfix, hcomm, hnil, hind, hker, ?_, ?_⟩
  · intro g hg
    apply element_of_extendedF_subring_not_coordinate hn g
    have hmem := (hker g).mp hg
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq.symm⟩
  · intro i
    simp [withOrdinaryExtras]

end AbhyankarSathaye.CommutingDerivations

end

end OAI

-- ---- mission target ----
open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
open MvPolynomial

theorem solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) ∧
      (∀ i : Fin (n-4), d (blocksToOutput hn (Sum.inl i)) =
        pderiv (blocksToAmbient hn (Sum.inl i))) := by
  first
    | exact OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras n hn
    | exact OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
    | (apply OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras <;> assumption)
    | (intros; apply OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras <;> assumption)
