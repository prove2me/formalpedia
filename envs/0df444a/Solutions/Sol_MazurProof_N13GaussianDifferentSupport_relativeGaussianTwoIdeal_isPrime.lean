-- Prove2me | solution 1 for MazurProof.N13GaussianDifferentSupport.relativeGaussianTwoIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T04:59:01.947964+00:00
-- url     : https://prove2.me/submissions/b18b8a84-8b08-408d-a8be-70538502be1b

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_h_explicit


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianDifferentSupport
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare

namespace MazurProof.N13GaussianCubicField
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
/-- The power basis on the generated Gaussian order, transported to the
proved relative integral closure. -/
def relativeIntegralPowerBasis :
    PowerBasis GI (integralClosure GI L) :=
  (Algebra.adjoin.powerBasis' (R := GI) alpha_integral).map
    (Subalgebra.equivOfEq _ _
      integralClosure_eq_adjoin.symm)
end
end MazurProof.N13GaussianCubicField

namespace MazurProof.N13GaussianCubicField
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL MazurProof.N13GaussianCubicField.fieldL
@[simp] theorem coe_relativeIntegralPowerBasis_gen :
    ((relativeIntegralPowerBasis.gen :
        integralClosure GI L) : L) = alpha := by
  simp [relativeIntegralPowerBasis]
end
end MazurProof.N13GaussianCubicField

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
def relativeAlpha : RelativeO :=
  N13GaussianCubicField.relativeIntegralPowerBasis.gen
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianDifferentSupport.fieldL
@[simp] theorem minpoly_relativeAlpha :
    minpoly GI relativeAlpha =
      N13GaussianGlobalArithmetic.h := by
  apply Polynomial.map_injective
    (f := algebraMap GI K)
    (FaithfulSMul.algebraMap_injective GI K)
  have halpha : IsIntegral GI relativeAlpha :=
    PowerBasis.isIntegral_gen
      N13GaussianCubicField.relativeIntegralPowerBasis
  calc
    (minpoly GI relativeAlpha).map
          (algebraMap GI K) =
        minpoly K
          (algebraMap RelativeO L relativeAlpha) :=
      (minpoly.isIntegrallyClosed_eq_field_fractions
        K L halpha).symm
    _ = minpoly K N13GaussianCubicField.alpha := by
      rw [show
        algebraMap RelativeO L relativeAlpha =
            N13GaussianCubicField.alpha by
          change
            ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
                RelativeO) : L) =
              N13GaussianCubicField.alpha
          exact
            N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]
    _ = N13GaussianCubicField.hK := by
      change
        minpoly K
            (AdjoinRoot.root N13GaussianCubicField.hK) =
          N13GaussianCubicField.hK
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
        N13GaussianCubicField.hK_monic
    _ =
        N13GaussianGlobalArithmetic.h.map
          (algebraMap GI K) := rfl
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
@[simp] theorem gaussianTwoInteger_norm :
    Zsqrtd.norm gaussianTwoInteger = 2 := by
  norm_num [gaussianTwoInteger,
    N13GaussianGlobalArithmetic.i, Zsqrtd.norm]
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
theorem absNorm_gaussianTwoIdeal :
    Ideal.absNorm gaussianTwoIdeal = 2 := by
  rw [gaussianTwoIdeal, Ideal.absNorm_span_singleton,
    N13GaussianFractionField.algebraNorm_eq_gaussianNorm,
    gaussianTwoInteger_norm]
  norm_num
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
theorem gaussianTwoIdeal_isPrime :
    gaussianTwoIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_gaussianTwoIdeal]
  exact Nat.irreducible_iff_prime.mpr
    (Nat.prime_iff.mp Nat.prime_two)
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
theorem gaussianTwoIdeal_ne_bot :
    gaussianTwoIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_gaussianTwoIdeal, Ideal.absNorm_bot] at this
  norm_num at this
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
@[simp] theorem gaussianI_mod_gaussianTwo :
    Ideal.Quotient.mk gaussianTwoIdeal
        N13GaussianGlobalArithmetic.i =
      (1 : GaussianTwoResidue) := by
  change
    Ideal.Quotient.mk gaussianTwoIdeal
        N13GaussianGlobalArithmetic.i =
      Ideal.Quotient.mk gaussianTwoIdeal (1 : GI)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    gaussianTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  ext <;>
    norm_num [gaussianTwoInteger,
      N13GaussianGlobalArithmetic.i]
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
@[simp] theorem two_eq_zero_mod_gaussianTwo :
    (2 : GaussianTwoResidue) = 0 := by
  change
    Ideal.Quotient.mk gaussianTwoIdeal (2 : GI) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (2 : GI) ∈ gaussianTwoIdeal
  rw [gaussianTwoIdeal, Ideal.mem_span_singleton]
  refine
    ⟨1 + N13GaussianGlobalArithmetic.i, ?_⟩
  ext <;>
    norm_num [gaussianTwoInteger,
      N13GaussianGlobalArithmetic.i]
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
/-- Modulo `1-i`, Frobenius gives `x²=x`; hence the reduced cubic has
value `1` at every element. -/
theorem gaussianTwoResidueCubic_irreducible :
    Irreducible gaussianTwoResidueCubic := by
  letI : gaussianTwoIdeal.IsMaximal :=
    gaussianTwoIdeal_isPrime.isMaximal gaussianTwoIdeal_ne_bot
  letI : Field GaussianTwoResidue :=
    Ideal.Quotient.field gaussianTwoIdeal
  letI : Finite GaussianTwoResidue :=
    (Ideal.absNorm_ne_zero_iff gaussianTwoIdeal).mp (by
      rw [absNorm_gaussianTwoIdeal]
      norm_num)
  letI : Fintype GaussianTwoResidue :=
    Fintype.ofFinite _
  have hcard :
      Fintype.card GaussianTwoResidue = 2 := by
    rw [← Nat.card_eq_fintype_card,
      ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply,
      absNorm_gaussianTwoIdeal]
  letI : CharP GaussianTwoResidue 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr
      two_eq_zero_mod_gaussianTwo
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    have hdeg :
        gaussianTwoResidueCubic.natDegree = 3 := by
      unfold gaussianTwoResidueCubic
      compute_degree!
    rw [hdeg]
    norm_num
  intro x hx
  have hcubic :
      x ^ 3 + x ^ 2 + 1 = 0 := by
    simpa [gaussianTwoResidueCubic,
      Polynomial.IsRoot, Polynomial.eval_add,
      Polynomial.eval_pow] using hx
  have hx2 : x ^ 2 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hx3 : x ^ 3 = x := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ = x * x := by rw [hx2]
      _ = x ^ 2 := by ring
      _ = x := hx2
  have hxx : x + x = 0 := by
    calc
      x + x = 2 * x := by ring
      _ = 0 := by rw [two_eq_zero_mod_gaussianTwo,
        zero_mul]
  rw [hx3, hx2, hxx, zero_add] at hcubic
  exact one_ne_zero hcubic
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
theorem map_h_mod_gaussianTwo :
    Polynomial.map
        (Ideal.Quotient.mk gaussianTwoIdeal)
        N13GaussianGlobalArithmetic.h =
      gaussianTwoResidueCubic := by
  rw [N13GaussianGlobalArithmetic.h_explicit]
  simp only [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_add, map_mul, map_pow,
    map_one, map_ofNat, Polynomial.map_one,
    Polynomial.map_ofNat]
  rw [N13GaussianGlobalArithmetic.pi,
    gaussianI_mod_gaussianTwo]
  simp only [map_sub, map_mul, map_ofNat,
    gaussianI_mod_gaussianTwo]
  simp only [Polynomial.C_1, one_pow, one_mul,
    mul_one]
  unfold gaussianTwoResidueCubic
  have htwo :
      (2 : GaussianTwoResidue[X]) = 0 := by
    change C (2 : GaussianTwoResidue) = 0
    rw [two_eq_zero_mod_gaussianTwo, map_zero]
  linear_combination
    (X ^ 2 + 52 * X + 162) * htwo
end
end MazurProof.N13GaussianDifferentSupport

namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL MazurProof.N13GaussianDifferentSupport.dedekindRelativeO MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO
theorem relativeGaussianTwoIdeal_irreducible :
    Irreducible relativeGaussianTwoIdeal := by
  unfold relativeGaussianTwoIdeal
  apply KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly
    (x := relativeAlpha)
    (gaussianTwoIdeal_isPrime.isMaximal
      gaussianTwoIdeal_ne_bot)
    gaussianTwoIdeal_ne_bot
  · rw [show
      conductor GI relativeAlpha = ⊤ by
        exact conductor_eq_top_of_powerBasis
          N13GaussianCubicField.relativeIntegralPowerBasis]
    simp
  · exact
      PowerBasis.isIntegral_gen
        N13GaussianCubicField.relativeIntegralPowerBasis
  · rw [minpoly_relativeAlpha, map_h_mod_gaussianTwo]
    exact gaussianTwoResidueCubic_irreducible
end
end MazurProof.N13GaussianDifferentSupport

attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
theorem solution : relativeGaussianTwoIdeal.IsPrime := by
  exact Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      relativeGaussianTwoIdeal_irreducible)
