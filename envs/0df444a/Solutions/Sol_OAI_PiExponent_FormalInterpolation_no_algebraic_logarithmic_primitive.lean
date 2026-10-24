-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.no_algebraic_logarithmic_primitive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:44:24.611986+00:00
-- url     : https://prove2.me/submissions/fdef6cac-b7a3-43b7-90cf-fd73003c89b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Differential.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_rational_presentation_at_transcendental
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ratFunc_euler_constant_obstruction
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_trace_commutes_with_compatible_derivations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

/-- Use Mathlib's finite differential-field extension, and recover linearity
over any field of constants in the original derivation. -/
theorem finiteExtensionDerivationLift_48f7595f
    (k L E : Type) [Field k] [Field L] [Field E] [CharZero L]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] [FiniteDimensional L E]
    (d : Derivation k L L) :
    ∃ D : Derivation k E E,
      ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a) := by
  letI : Differential L := ⟨d.restrictScalars ℤ⟩
  letI : Differential E := Differential.differentialFiniteDimensional L E
  letI : DifferentialAlgebra L E :=
    Differential.differentialAlgebraFiniteDimensional (F := L) (K := E)
  have hconstant (a : k) :
      Differential.deriv (algebraMap k E a) = 0 := by
    rw [IsScalarTower.algebraMap_apply k L E, deriv_algebraMap]
    change algebraMap L E (d (algebraMap k L a)) = 0
    simp
  let D : Derivation k E E :=
    { toLinearMap :=
        { toFun := Differential.deriv
          map_add' := fun a b => map_add Differential.deriv a b
          map_smul' := by
            intro a x
            simp only [RingHom.id_apply, Algebra.smul_def]
            simp only [Derivation.leibniz, hconstant, smul_eq_mul, mul_zero, add_zero] }
      map_one_eq_zero' := Derivation.map_one_eq_zero Differential.deriv
      leibniz' := fun a b => Derivation.leibniz Differential.deriv a b }
  refine ⟨D, ?_⟩
  intro a
  exact deriv_algebraMap a

theorem solution
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (y z : E)
    (hprimitive : ∀ D : Derivation Complex E E, D z = D y / y) :
    ∃ a : Complex, y = algebraMap Complex E a := by
  classical
  by_cases hy : IsAlgebraic Complex y
  · have hi : IsIntegral Complex y := hy.isIntegral
    have hq : (minpoly Complex y).leadingCoeff = 1 := minpoly.monic hi
    have hdegree : (minpoly Complex y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible Complex (minpoly.irreducible hi)
    have heval : Polynomial.aeval y (minpoly Complex y) = 0 :=
      minpoly.aeval Complex y
    rw [Polynomial.eq_X_add_C_of_degree_eq_one hdegree, hq, Polynomial.C_1,
      one_mul, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
      add_eq_zero_iff_eq_neg] at heval
    exact ⟨-(minpoly Complex y).coeff 0, by simpa only [map_neg] using heval⟩
  · obtain ⟨K, f, hfy, hfinite⟩ :=
      finite_rational_presentation_at_transcendental Complex E y hy
    letI : Algebra (RatFunc K) E := f.toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc K) E := hfinite
    letI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algHom f
    obtain ⟨d, hdX, hdconstant⟩ := ratFunc_euler_constant_obstruction K
    obtain ⟨D, hcompat⟩ := finiteExtensionDerivationLift_48f7595f K (RatFunc K) E d
    have hyzero : y ≠ 0 := by
      intro hz
      apply RatFunc.X_ne_zero (K := K)
      apply f.injective
      change f RatFunc.X = f 0
      exact hfy.trans (hz.trans (map_zero f).symm)
    have hDy : D y = y := by
      calc
        D y = D (f RatFunc.X) := congrArg D hfy.symm
        _ = f (d RatFunc.X) := hcompat RatFunc.X
        _ = f RatFunc.X := congrArg f hdX
        _ = y := hfy
    have hDz : D z = 1 := by
      have h := hprimitive (D.restrictScalars Complex)
      change D z = D y / y at h
      simpa only [hDy, div_self hyzero] using h
    have htrace :=
      trace_commutes_with_compatible_derivations K (RatFunc K) E d D hcompat z
    have htraceone : Algebra.trace (RatFunc K) E (1 : E) =
        (Module.finrank (RatFunc K) E : RatFunc K) := by
      simpa only [map_one, nsmul_eq_mul, mul_one] using
        (Algebra.trace_algebraMap (R := RatFunc K) (S := E) (1 : RatFunc K))
    have hn : (Module.finrank (RatFunc K) E : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
    apply False.elim
    apply hdconstant (Algebra.trace (RatFunc K) E z)
      (Module.finrank (RatFunc K) E : K) hn
    simpa only [hDz, htraceone, map_natCast] using htrace
