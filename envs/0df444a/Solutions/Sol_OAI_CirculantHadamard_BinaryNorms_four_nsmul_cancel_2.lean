-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:08:56.838473+00:00
-- url     : https://prove2.me/submissions/62c33ace-2c9c-4546-9556-6f04497c899f

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryNorms.lean:L37-L53
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryNorms ----
namespace OAI

universe uR uA

/-!
# Cancelling the factor four in the binary norm identities

The coefficient ring may be a domain; the finite cyclic group algebra is not
assumed to be a domain. Cancellation is performed separately at every
coefficient. In particular these statements apply both to complex coefficients
and to the actual Gaussian subring of `ℂ`.

`CyclicRing.ringStar` conjugates coefficients as well as reversing exponents.
The evaluation bridge requires compatibility with this full operation,
including at the fourth root `i`; an inversion-only operation would not suffice.
-/

noncomputable section

namespace CirculantHadamard.BinaryNorms

open CyclicRing

section CoefficientCancellation

variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}

/-- Cancel four coefficientwise, without any domain assumption on the group
algebra. -/
theorem four_nsmul_cancel {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  let coeff : Elem R n →+ R :=
    { toFun := fun p => p.coeff a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have ha := congrArg coeff h
  rw [map_nsmul, map_nsmul] at ha
  have hc : (4 : R) * f.coeff a = (4 : R) * g.coeff a := by
    simp only [coeff, nsmul_eq_mul, Nat.cast_ofNat] at ha
    convert ha using 1 <;> rfl
  exact mul_left_cancel₀ (by norm_num : (4 : R) ≠ 0) hc

end CoefficientCancellation

section NormCancellation

variable {R : Type uR} [CommRing R] [StarRing R]
variable {n : ℕ} [NeZero n]

variable [IsDomain R] [CharZero R]

end NormCancellation

section ActualBinaryElements

open BinaryBlocks BinaryCoefficients

variable {m : ℕ} [NeZero m]

end ActualBinaryElements

end CirculantHadamard.BinaryNorms

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryNorms
open CyclicRing


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel.{uR} := @_root_.OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel.{uR}
