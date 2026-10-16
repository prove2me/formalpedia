-- Prove2me | solution 1 for MIPRE.Halting.halting_reduction_both_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:59:03.743201+00:00
-- url     : https://prove2.me/submissions/300ddf83-9e23-4b02-9159-6eb735c8006a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorProgram.lean (solution of MIPRE.Halting.halting_reduction_both_of);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_CompressorCost
import Definitions.Def_MIPRE_Foundations_Halting_CompressorProgram
import Theorems.Thm_MIPRE_Cost_Data_primrec_decode_prod_nat
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_runs_of_runForD
import Theorems.Thm_MIPRE_Cost_Prog_wrapCore_hasPolyCost
import Theorems.Thm_MIPRE_Cost_compressibility_criterion_levels
import Theorems.Thm_MIPRE_Cost_exists_compile
import Theorems.Thm_MIPRE_Cost_exists_semidecider_of_decode
import Theorems.Thm_MIPRE_Halting_exists_compressorSpec
import Theorems.Thm_MIPRE_Halting_primrec_tabOf
import Theorems.Thm_MIPRE_Halting_tab_match
import Theorems.Thm_MIPRE_Halting_yYes_mem
import Theorems.Thm_MIPRE_REPred_of_computable_exists
import Theorems.Thm_MIPRE_Verifier_exists_isBounded_lam
import Theorems.Thm_MIPRE_Verifier_freeze_hasPerfectPCC
import Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_accepts_iff
import Theorems.Thm_MIPRE_Verifier_rePred_not_isBounded
import Theorems.Thm_MIPRE_tracialValue_le_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TracialState
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- The trace of a product of two projections is nonnegative:
`τ (p * q) = τ (star (q * p) * (q * p))`. This is the positivity of outcome
probabilities for the strategies below. -/
theorem nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ τ (p * q) := by
  have key : star (q * p) * (q * p) = p * q * p := by
    rw [star_mul, hps, hqs, mul_assoc p q (q * p), ← mul_assoc q q p, hqq, ← mul_assoc]
  calc (0 : ℂ) ≤ τ (star (q * p) * (q * p)) := τ.star_mul_self_nonneg _
    _ = τ (p * q * p) := by rw [key]
    _ = τ (p * q) := by rw [τ.map_mul_comm (p * q) p, ← mul_assoc, hpp]
end MIPRE.TracialState

namespace MIPRE.TracialState
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- Real-part form of `TracialState.nonneg_mul`. -/
theorem re_nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ (τ (p * q)).re := by
  simpa using (Complex.le_def.mp (τ.nonneg_mul hps hpp hqs hqq)).1
end MIPRE.TracialState

namespace MIPRE
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
/-- The generic value is nonnegative. -/
theorem tracialValue_nonneg (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : 0 ≤ tracialValue G τ P := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have hre : 0 ≤ (τ (P.M x a * P.M y b)).re :=
    τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b)
      (P.projective y b)
  have hind : (0 : ℝ) ≤ if G.D x y a b then 1 else 0 := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (G.μ_nonneg x y) hind) hre
end MIPRE

namespace MIPRE.SyncStrategy
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
variable {G : SynchronousGame X A}
/-- The value of a synchronous strategy is nonnegative. -/
theorem value_nonneg (S : SyncStrategy G) : 0 ≤ S.value :=
  tracialValue_nonneg G _ S.P
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
variable {G : SynchronousGame X A}
/-- The value of a synchronous strategy is at most one. -/
theorem value_le_one (S : SyncStrategy G) : S.value ≤ 1 :=
  tracialValue_le_one G _ S.P
end MIPRE.SyncStrategy

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

namespace MIPRE
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
/-- The synchronous value lower-bounds the quantum value (blueprint
`lem:sync-le-valstar`): a synchronous strategy `{M^x_a}` on `ℂ^d` yields the
tensor-product strategy `A^x_a = M^x_a`, `B^y_b = (M^y_b)ᵀ`,
`ψ = d^{-1/2} ∑ᵢ |i⟩|i⟩` with the same value
(`SyncStrategy.value_toTensorProductStrategy`). -/
theorem syncValue_le_quantumValue (G : SynchronousGame X A) :
    syncValue G ≤ quantumValue G.toGame := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  rw [← S.value_toTensorProductStrategy]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value _) S.toTensorProductStrategy
end MIPRE

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_copy_le (S : TensorProductStrategy G) (G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.re_dotProduct_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]
end MIPRE.TensorProductStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- The quantum value is at most one. -/
theorem quantumValue_le_one (G : Game X Y A B) : quantumValue G ≤ 1 :=
  Real.iSup_le (fun S => S.value_le_one) zero_le_one
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- Games related by equivalences of their alphabets, with matching distribution and
decision predicate, have the same quantum value. -/
theorem quantumValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G)
      (S'.relabel G eX.symm eY.symm eA.symm eB.symm)
    rwa [S'.value_relabel G eX.symm eY.symm eA.symm eB.symm (fun x y => by simp [hμ])
      (fun x y a b => by simp [hD])] at h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G')
      (S.relabel G' eX eY eA eB)
    rwa [S.value_relabel G' eX eY eA eB hμ hD] at h
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- Accepting more answer tuples, on the same alphabets and distribution, raises the quantum
value. -/
theorem quantumValue_mono (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  exact (S.value_copy_le G' hμ hD).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value G') (S.copy G'))
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- A game whose decision predicate rejects everything has quantum value `0`. -/
theorem quantumValue_eq_zero_of_reject (G : Game X Y A B) (hD : ∀ x y a b, G.D x y a b = false) :
    quantumValue G = 0 := by
  refine le_antisymm (Real.iSup_le (fun S => ?_) le_rfl) (quantumValue_nonneg G)
  unfold TensorProductStrategy.value
  simp [hD]
end MIPRE

namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' ≃ X) (eA : A' ≃ A)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eX y') (eA a') (eA b')) :
    (S.relabel G' eX eA).value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      ((S.P.M (eX x') (eA a') * S.P.M (eX y') (eA b')).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eX.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eA.symm _ _ fun b => ?_
  simp only [hμ, hD, Equiv.apply_symm_apply]
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
/-- Relabeling preserves the PCC property: the operators of the relabeled strategy are
operators of the original one, at question pairs that keep their weight. -/
theorem isPCC_relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X' A') (eX : X' → X)
    (eA : A' ≃ A) (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y')) :
    (S.relabel G' eX eA).IsPCC := by
  intro x' y' hxy a' b'
  rw [hμ] at hxy
  exact hS _ _ hxy _ _
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
/-- The values of synchronous strategies are bounded above (by one). -/
theorem bddAbove_range_value (G : SynchronousGame X A) :
    BddAbove (Set.range fun S : SyncStrategy G => S.value) := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, rfl⟩
  exact S.value_le_one
end MIPRE.SyncStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- The synchronous value is nonnegative. -/
theorem syncValue_nonneg [DecidableEq A] (G : SynchronousGame X A) : 0 ≤ syncValue G :=
  Real.iSup_nonneg fun S => S.value_nonneg
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- The synchronous value is at most one. -/
theorem syncValue_le_one [DecidableEq A] (G : SynchronousGame X A) : syncValue G ≤ 1 :=
  Real.iSup_le (fun S => S.value_le_one) zero_le_one
end MIPRE

namespace HaltingGameValue.GameData
theorem value_toSyncStrategy (g : GameData) (S : SyncStrategy g.toGame) :
    (g.toSyncStrategy S).value = strategyValue g.toGame S := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
theorem strategyValue_ofSyncStrategy (g : GameData) (S : MIPRE.SyncStrategy g.syncGame) :
    strategyValue g.toGame (g.ofSyncStrategy S) = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
theorem strategyValue_nonneg (g : GameData) (S : SyncStrategy g.toGame) :
    0 ≤ strategyValue g.toGame S := by
  rw [← value_toSyncStrategy]
  exact (g.toSyncStrategy S).value_nonneg
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
theorem strategyValue_le_one (g : GameData) (S : SyncStrategy g.toGame) :
    strategyValue g.toGame S ≤ 1 := by
  rw [← value_toSyncStrategy]
  exact (g.toSyncStrategy S).value_le_one
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
theorem bddAbove_range_strategyValue (g : GameData) :
    BddAbove (Set.range fun S : SyncStrategy g.toGame => strategyValue g.toGame S) := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, rfl⟩
  exact g.strategyValue_le_one S
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
theorem gameValue_nonneg (g : GameData) : 0 ≤ gameValue g.toGame :=
  Real.iSup_nonneg fun S => g.strategyValue_nonneg S
end HaltingGameValue.GameData

namespace HaltingGameValue.GameData
/-- **The two synchronous values agree.** `HaltingGameValue.gameValue`, the value in which the
headline `HaltingGameValue.halting_reduces_to_gameValue` is stated, is `MIPRE.syncValue` of the
same description read in the foundations. -/
theorem gameValue_eq_syncValue (g : GameData) :
    gameValue g.toGame = MIPRE.syncValue g.syncGame := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (MIPRE.syncValue_nonneg _)
    rw [← g.value_toSyncStrategy S]
    exact le_ciSup (MIPRE.SyncStrategy.bddAbove_range_value _) (g.toSyncStrategy S)
  · refine Real.iSup_le (fun S => ?_) g.gameValue_nonneg
    rw [← g.strategyValue_ofSyncStrategy S]
    exact le_ciSup (g.bddAbove_range_strategyValue) (g.ofSyncStrategy S)
end HaltingGameValue.GameData

namespace MIPRE.Cost
/-- A polynomial-time function of the ambient model, precomposed with a computable
encoding of its input and followed by a computable decoding of its output, is
Mathlib-computable. -/
theorem PolyTimeFun.computable_comp {α β γ : Type*} [SizedEncoding α] [SizedEncoding β]
    [Primcodable γ] [Primcodable β] [Inhabited β] (F : PolyTimeFun α β) (h : γ → α)
    (hh : Computable fun c => (encode (h c) : Data))
    (hβ : Computable fun d : Data => (SizedEncoding.decode d : Option β)) :
    Computable fun c => F (h c) := by
  have h2 : Computable fun c => (SizedEncoding.decode (encode (F (h c)) : Data) : Option β) :=
    hβ.comp (F.computable_encode_comp h hh)
  refine (Primrec.option_getD_default.to_comp.comp h2).of_eq fun c => ?_
  simp [SizedEncoding.decode_encode]
end MIPRE.Cost

namespace MIPRE.Game
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The one computation the doubling needs, in a form independent of what kind of strategy is
being summed: the four-fold sum over the doubled alphabets collapses to the original one, the
three blocks other than `(false, ·), (true, ·)` contributing zero. -/
theorem sum_doubled (G : Game X X A A) (f : (Bool × X) → (Bool × X) → A → A → ℝ) :
    (∑ p, ∑ q, ∑ a, ∑ b,
        G.doubled.μ p q * (if G.doubled.D p q a b then 1 else 0) * f p q a b)
      = ∑ x, ∑ y, ∑ a, ∑ b,
          G.μ x y * (if G.D x y a b then 1 else 0) * f (false, x) (true, y) a b := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubled_μ, doubled_D]
  simp
end MIPRE.Game

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    S.undouble.value = S.value := by
  rw [show S.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p a ⊗ₖ S.PB.M q b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_double {G : Game X X A A} (S : TensorProductStrategy G) :
    S.double.value = S.value := by
  rw [show S.double.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p.2 a ⊗ₖ S.PB.M q.2 b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end MIPRE.TensorProductStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- **The doubling preserves the quantum value.** Each direction is one strategy transported
and one `le_ciSup`; `TensorProductStrategy` carries no field mentioning the game, so `relabel`
is a bijection of the two index types of the supremum. -/
theorem quantumValue_doubled (G : Game X X A A) :
    quantumValue G.doubled.toGame = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_undouble]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) S.undouble
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_double]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G.doubled.toGame) S.double
end MIPRE

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **The doubled game has the value it doubles**, with no synchronicity hypothesis. -/
theorem quantumValue_doubledGame (n T : ℕ) :
    quantumValue (V.doubledGame n T).toGame = V.valStar n T :=
  quantumValue_doubled (V.game n T)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- With the same sampler, a decider accepting more at index `n` gives a larger `val*`. -/
theorem valStar_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valStar n T ≤ W.valStar n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine quantumValue_mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
`val*`. -/
theorem valStar_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  le_antisymm (valStar_le_of_accepts_imp hS fun x y a b => (h x y a b).1)
    (valStar_le_of_accepts_imp hS.symm fun x y a b => (h x y a b).2)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem hasPerfectPCC_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.HasPerfectPCC n T ↔ W.HasPerfectPCC n T :=
  ⟨hasPerfectPCC_of_accepts_iff hS h,
    hasPerfectPCC_of_accepts_iff hS.symm fun x y a b => (h x y a b).symm⟩
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A perfect PCC strategy gives quantum value `1`. -/
theorem valStar_eq_one_of_hasPerfectPCC {n T : ℕ} (h : V.HasPerfectPCC n T) :
    V.valStar n T = 1 := by
  obtain ⟨S, -, hval⟩ := h
  refine le_antisymm (quantumValue_le_one _) ?_
  have h1 := le_ciSup (TensorProductStrategy.bddAbove_range_value
    (V.doubledGame n T).toGame) S.toTensorProductStrategy
  rw [SyncStrategy.value_toTensorProductStrategy, hval] at h1
  rw [← V.quantumValue_doubledGame n T]
  exact h1
end MIPRE.Verifier

namespace MIPRE.Cost.Prog
open Cost
/-- The description of the frozen program: that of `p`, plus the index, plus `53` nodes. -/
theorem esize_freezeProg (k : ℕ) (p : Prog) : esize (freezeProg k p) = esize p + esize k + 53 := by
  rw [esize_eq_size_toData, esize_eq_size_toData]
  unfold esize
  simp only [freezeProg, Prog.toData, Data.size_cons, Data.size_ofNat, Data.size_nil]
  omega
end MIPRE.Cost.Prog

namespace MIPRE
open Cost
/-- The arithmetic shared by the two freezing time bounds: the frozen program's cost fits
under the same polynomial with the coefficient shifted by the cost of copying, once the
degree is at least one. -/
theorem freeze_cost_le {T j e t s : ℕ} (ht : t ≤ T * (s + 1) ^ j) :
    t + e + s + 4 ≤ (T + e + 4) * (s + 1) ^ max j 1 := by
  have h1 : (s + 1) ^ j ≤ (s + 1) ^ max j 1 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : s + 1 ≤ (s + 1) ^ max j 1 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ max j 1 := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h3 : (T + e + 4) * (s + 1) ^ max j 1 =
      T * (s + 1) ^ max j 1 + (e + 4) * (s + 1) ^ max j 1 := by ring
  have h4 : (e + 4) * (s + 1) ≤ (e + 4) * (s + 1) ^ max j 1 := Nat.mul_le_mul_left _ h2
  have h5 : T * (s + 1) ^ j ≤ T * (s + 1) ^ max j 1 := Nat.mul_le_mul_left _ h1
  nlinarith
end MIPRE

namespace MIPRE.CL.Sampler
open Cost
variable {ℓ : ℕ} (S : Sampler ℓ)
theorem freeze_size (k : ℕ) : (S.freeze k).size = S.size + esize k + 53 :=
  Prog.esize_freezeProg k S.prog
end MIPRE.CL.Sampler

namespace MIPRE.CL.Sampler
open Cost
variable {ℓ : ℕ} (S : Sampler ℓ)
/-- The frozen sampler's running time at any index is that of `S` at the frozen index, up
to the cost of copying the input. -/
theorem freeze_timeBoundAt {k T j : ℕ} (h : S.TimeBoundAt k T j) (n : ℕ) :
    (S.freeze k).TimeBoundAt n (T + esize k + 4) (max j 1) := by
  intro d
  obtain ⟨r, t, ht, hrun⟩ := h d
  exact ⟨r, t + esize k + d.size + 4, freeze_cost_le ht, Prog.freezeProg_runs S.closed hrun⟩
end MIPRE.CL.Sampler

namespace MIPRE.Decider
open Cost
variable (D : Decider)
theorem freeze_size (k : ℕ) : (D.freeze k).size = D.size + esize k + 53 :=
  Prog.esize_freezeProg k D.prog
end MIPRE.Decider

namespace MIPRE.Decider
open Cost
variable (D : Decider)
theorem freeze_timeBoundAt {k T j : ℕ} (h : D.TimeBoundAt k T j) (n : ℕ) :
    (D.freeze k).TimeBoundAt n (T + esize k + 4) (max j 1) := by
  intro d
  obtain ⟨r, t, ht, hrun⟩ := h d
  exact ⟨r, t + esize k + d.size + 4, freeze_cost_le ht, Prog.freezeProg_runs D.closed hrun⟩
end MIPRE.Decider

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem freeze_size (k : ℕ) : (V.freeze k).size = V.size + esize k + 53 := by
  simp only [size, freeze_sampler, freeze_decider, CL.Sampler.freeze_size, Decider.freeze_size]
  omega
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- The value of the frozen verifier at any index is the value of `V` at the frozen index. -/
theorem freeze_valStar (k n T : ℕ) : (V.freeze k).valStar n T = V.valStar k T := by
  unfold valStar
  refine quantumValue_eq_of_equiv (V.game k T) ((V.freeze k).game n T) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (fun _ _ => rfl) fun x y a b => ?_
  exact decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **`λ`-boundedness of the frozen verifier.** The frozen verifier is `λ`-bounded when the
dimension and the running times of `V` at the frozen index, shifted by the cost of freezing,
fit under `2 ^ λ`, and its size, shifted by the size of the index, fits under `λ`. -/
theorem freeze_isBounded (k lam TS TD jS jD : ℕ) (hS : V.sampler.TimeBoundAt k TS jS)
    (hD : V.decider.TimeBoundAt k TD jD) (hdim : V.sampler.dim k ≤ 2 ^ lam)
    (hTS : TS + esize k + 4 ≤ 2 ^ lam) (hTD : TD + esize k + 4 ≤ 2 ^ lam)
    (hjS : max jS 1 ≤ lam) (hjD : max jD 1 ≤ lam)
    (hsize : V.size + esize k + 53 ≤ lam) : (V.freeze k).IsBounded lam := by
  refine ⟨fun n hn => ?_, ?_⟩
  · have h2 : 2 ^ lam ≤ n ^ lam := Nat.pow_le_pow_left hn lam
    refine ⟨?_, ?_, ?_⟩
    · exact (V.sampler.freeze_dim k n).le.trans (hdim.trans h2)
    · exact (V.sampler.freeze_timeBoundAt hS n).mono (hTS.trans h2) hjS
    · exact (V.decider.freeze_timeBoundAt hD n).mono (hTD.trans h2) hjD
  · rw [V.freeze_size k]; exact hsize
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A decider that accepts nothing at index `n` gives quantum value `0`. -/
theorem valStar_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valStar n T = 0 := by
  classical
  refine quantumValue_eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A verifier that accepts nothing at index `n` and is `n`-bounded is in the class `B`. -/
theorem inClassB_of_rejects_all {n T : ℕ} (hb : V.IsBounded n)
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.InClassB n T := by
  refine ⟨hb, fun x y a b _ => hrej x y a b, ?_⟩
  rw [V.valStar_eq_zero_of_rejects_all hrej]
  norm_num
end MIPRE.Verifier

namespace MIPRE.Decider
open Cost
open Cost Cost.Prog
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data)
/-- Acceptance when the datum is the encoding of a program `dec`: the universal machine's run
is a run of `dec` (`UniversalMachine.time_le`, `halts_of`). -/
theorem wrap_accepts_prog (dec : Prog) (n : ℕ) (x y a b : BitStr) :
    (wrap U S (encode dec)).Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) := by
  rw [wrap_accepts]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun ⟨t, h⟩ => ?_, fun ⟨t, h⟩ => ?_⟩
  · exact U.halts_of dec _ _ _ h
  · obtain ⟨t', -, h'⟩ := U.time_le dec _ _ t h
    exact ⟨t', h'⟩
end MIPRE.Decider

namespace MIPRE.Verifier
open Cost
open Cost
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data) (dec : Prog)
theorem ofSamplerDecider_accepts (n : ℕ) (x y a b : BitStr) :
    (ofSamplerDecider U S dec).decider.Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) :=
  Decider.wrap_accepts_prog U S dec n x y a b
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open Cost Cost.Data
open HaltingGameValue (GameData)
/-- **The complement of the class `B`**, as the criterion's semidecider has to see it: either
the verifier is not `n`-bounded — witnessed by a single input whose run exceeds the budget, so
a search — or its value at index `n` exceeds `1/2`, which is the `val*` half of
`lem:value-lower-approx` on the tabulation. Neither disjunct decides `n`-boundedness, which is
`Π₁`; the point of the disjunction is that it does not have to. -/
theorem not_inClassB_iff {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) :
    ¬ V.InClassB n T ↔
      (¬ V.IsBounded n ∨ ¬ V.RejectsLong n T ∨ 1 / 2 < V.valStar n T) := by
  rw [InClassB, not_and_or, not_and_or, not_le]
end MIPRE.Verifier

namespace MIPRE.Cost.Machine
/-- **The decision procedure.** For a program that halts within the budget, whether it returns
a given value is decidable. -/
theorem runForD_eq_some_iff {p : Prog} {x r : Data} {k : ℕ}
    (hb : HaltsWithin p x k) : runForD (encode p) x k = some r ↔ ∃ t, p.Runs x r t := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb
  refine ⟨runs_of_runForD, fun ⟨t, h⟩ => ?_⟩
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact runForD_eq_some h₀ ht₀
end MIPRE.Cost.Machine

namespace MIPRE.Verifier
open Cost
/-- `λ`-boundedness is monotone in `λ`: every clause of `def:lambda-bounded` weakens as `λ`
grows. Raising `λ` is free, which is what lets a verifier bounded at some fixed `λ` belong to
the classes at every level above it. -/
theorem IsBounded.mono {ℓ : ℕ} {V : Verifier ℓ} {lam lam' : ℕ} (h : V.IsBounded lam)
    (hle : lam ≤ lam') : V.IsBounded lam' := by
  obtain ⟨hmain, hsize⟩ := h
  refine ⟨fun n hn => ?_, hsize.trans hle⟩
  obtain ⟨hdim, hS, hD⟩ := hmain n hn
  have hpow : n ^ lam ≤ n ^ lam' := Nat.pow_le_pow_right (by omega) hle
  exact ⟨hdim.trans hpow, hS.mono hpow hle, hD.mono hpow hle⟩
end MIPRE.Verifier

namespace MIPRE
open Cost
/-- A uniform time bound whose coefficient is polynomially bounded *is* polynomially bounded
cost. This is the direction `MIPRE.GapCompression` supplies: its `sampler_time` and
`decider_time` fields bound the running times of the compressed verifier by
`bound.eval (n + λ)` at a fixed degree, and `bound.eval (n + λ)` is polynomially bounded in
`n`. -/
theorem Cost.Prog.hasPolyCost_of_bound {p : Prog} {T : ℕ → ℕ} {k : ℕ} (hT : PolyBounded T)
    (h : ∀ (n : ℕ) (d : Data), HaltsWithin p (.cons (encode n) d) (T n * (d.size + 1) ^ k)) :
    p.HasPolyCost :=
  ⟨T, k, hT, fun n d => h n d⟩
end MIPRE

namespace MIPRE
open Cost
/-- The sampler form. -/
theorem CL.Sampler.hasPolyCost_of_timeBound {ℓ : ℕ} {S : CL.Sampler ℓ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolyBounded T) (h : ∀ n, S.TimeBoundAt n (T n) k) : S.prog.HasPolyCost :=
  Cost.Prog.hasPolyCost_of_bound hT fun n d => h n d
end MIPRE

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **The threshold form**: such a verifier is `n`-bounded at every level `n` from some `n₀` on.
This is the shape the classes `MIPRE.Halting.classA`, `classB` consume, `IsBounded n` being
asked at the level itself. -/
theorem exists_isBounded (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → V.IsBounded n := by
  obtain ⟨lam, hlam⟩ := V.exists_isBounded_lam hdim hS hD
  exact ⟨lam, fun _ hn => hlam.mono hn⟩
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The value bridge, doubled.** A game description matching `𝒱_n`'s *doubled* game along
relabelings of the two alphabets has the value of `𝒱_n` — the doubled replacement of
`quantumValue_toGame_eq_valStar`, and unlike it free of any synchronicity hypothesis. Note
that `hD` here is total, on every question pair including the diagonal: the doubled game
rejects off the tag block, exactly as a `GameData` does, so `quantumValue_eq_of_equiv` applies
unchanged and no support-restricted version of it is needed. -/
theorem quantumValue_toGame_eq_valStar_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l)) :
    quantumValue g.game = V.valStar n T := by
  rw [← V.quantumValue_doubledGame n T]
  exact quantumValue_eq_of_equiv (V.doubledGame n T).toGame g.game eX eX eA eA hμ hD
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The completeness bridge, doubled.** `HasPerfectPCC` is a strategy of the doubled game
already, so it is relabeled along the equivalences by `SyncStrategy.relabel` and nothing
else. -/
theorem exists_perfectPCC_syncGame_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    ∃ S : SyncStrategy g.syncGame, S.IsPCC ∧ S.value = 1 := by
  obtain ⟨S, hPCC, hval⟩ := hV
  refine ⟨S.relabel g.syncGame eX eA, S.isPCC_relabel hPCC g.syncGame eX eA hμ, ?_⟩
  rw [S.value_relabel g.syncGame eX eA hμ hD, hval]
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The completeness bridge, doubled, in the synchronous value.** -/
theorem syncValue_syncGame_eq_one_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    syncValue g.syncGame = 1 := by
  obtain ⟨S, -, hval⟩ := V.exists_perfectPCC_syncGame_doubled n T g eX eA hμ hD hV
  refine le_antisymm (syncValue_le_one _) ?_
  rw [← hval]
  exact le_ciSup (SyncStrategy.bddAbove_range_value _) S
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The completeness bridge, doubled, in the value of `HaltingGameValue`.** This is what
`MIPRE.Halting.gameValue_tab_eq_one` is proved from, and so what item 1 of blueprint
`thm:halting` rests on. -/
theorem gameValue_toGame_eq_one_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    HaltingGameValue.gameValue g.toGame = 1 := by
  rw [g.gameValue_eq_syncValue]
  exact V.syncValue_syncGame_eq_one_doubled n T g eX eA hμ hD hV
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The soundness bridge, doubled.** Its hypothesis is an upper bound on `val*` and nothing
is assumed of the decider. -/
theorem gameValue_toGame_le_of_valStar_le_doubled {c : ℝ}
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.valStar n T ≤ c) :
    HaltingGameValue.gameValue g.toGame ≤ c := by
  rw [g.gameValue_eq_syncValue]
  refine (syncValue_le_quantumValue g.syncGame).trans ?_
  rw [show g.syncGame.toGame = g.game from rfl,
    V.quantumValue_toGame_eq_valStar_doubled n T g eX eA hμ hD]
  exact hV
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem mem_classB_iff {n : ℕ} {x : BitStr} :
    x ∈ classB G U n ↔ (Vof G U x).InClassB n (ansBound G x n) := Iff.rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem primrec_tabOf_tuple (k : ℕ) :
    Primrec fun q : (Data × Data) × (ℕ × ℕ) × ℕ × ℕ =>
      tabOf q.1.1 q.1.2 q.2.1.1 q.2.2.1 q.2.1.2 k q.2.2.2 :=
  primrec_tabOf k (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem computable_tabArgs : Computable fun p : BitStr × ℕ =>
    ((sampData G p.1, decProgData G U p.1),
      ((dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2, ansBound G p.1 p.2),
        (ansBound G p.1 p.2, p.2))) :=
  ((computable_sampData_fst G).pair (computable_decProgData_fst G U)).pair
    (((computable_dimOf_fst G).pair (computable_ansBound G)).pair
      ((computable_ansBound G).pair Computable.snd))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- **O2, computability.** -/
theorem tab_computable : Computable fun p : BitStr × ℕ => tab G U p.1 p.2 :=
  ((primrec_tabOf_tuple G.deg).to_comp.comp (computable_tabArgs G U)).of_eq fun _ => rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem decProgData_eq (x : BitStr) : decProgData G U x = encode ((Vof G U x).decider.prog) := by
  rw [decProgData, sampData_eq, Prog.ProgD.dWrapCore_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- **O2, the value — doubled**: the tabulated game has the value of `𝒱_n` at *every*
`n`-bounded string, with no synchronicity hypothesis. This is `Halting.exists_sem_of_tab`'s
`hval`. -/
theorem tab_value (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    quantumValue (tab G U x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb
  exact Verifier.quantumValue_toGame_eq_valStar_doubled _ _ _ _ eX eA hμ hD
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- The completeness branch, in the value of `HaltingGameValue`. -/
theorem gameValue_tab_eq_one (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (hV : (Vof G U x).HasPerfectPCC n (ansBound G x n)) :
    HaltingGameValue.gameValue (tab G U x n).toGame = 1 := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb
  exact Verifier.gameValue_toGame_eq_one_doubled _ _ _ _ eX eA hμ hD hV
end MIPRE.Halting

namespace MIPRE.Cost
/-- The instance obligation **O3** asks for: an r.e. predicate on `(string, level)` pairs is
the halting set of a well-scoped program on `encode (x, n)`. -/
theorem exists_semidecider_prod_nat {p : BitStr → ℕ → Prop} (hp : REPred fun q : BitStr × ℕ =>
    p q.1 q.2) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ p x n :=
  let ⟨S, hws, hS⟩ := exists_semidecider_of_decode Data.primrec_decode_prod_nat hp
  ⟨S, hws, fun x n => hS (x, n)⟩
end MIPRE.Cost

namespace MIPRE
open Cost
open HaltingGameValue (GameData)
/-- **A union of two r.e. predicates is r.e.**, by dovetailing (`Partrec.merge'`). Mathlib has
the dovetailing but not this corollary of it. -/
theorem REPred.or {α : Type*} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  refine hk.dom_re.of_eq fun a => ?_
  rw [(H a).2]
  exact or_congr ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
    ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
end MIPRE

namespace MIPRE
open Cost
open HaltingGameValue (GameData)
/-- `≤` on naturals as a primitive recursive `Bool`-valued function. `Primrec.nat_le` is a
`PrimrecRel`, which hides the `Decidable` instance behind an existential and so does not
compose with `Computable` arguments; this is the same fact in usable form. -/
theorem Cost.primrec_natLeB : Primrec fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
  obtain ⟨_, h⟩ := Primrec.nat_le
  exact h.of_eq fun p => by rw [Bool.eq_iff_iff]; simp
end MIPRE

namespace MIPRE
open Cost
open HaltingGameValue (GameData)
/-- Equality on `Option Data` as a primitive recursive `Bool`-valued function, extracted from
`Primrec.eq` the way `primrec_natLeB` extracts `Primrec.nat_le`. -/
theorem Cost.primrec_optionDataEqB :
    Primrec fun p : Option Data × Option Data => decide (p.1 = p.2) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel fun a b : Option Data => a = b)
  exact h.of_eq fun p => by rw [Bool.eq_iff_iff]; simp
end MIPRE

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem longAcceptanceB_iff (n T : ℕ) (w : (BitStr × BitStr × BitStr × BitStr) × ℕ) :
    V.longAcceptanceB n T w = true ↔ V.LongAcceptance n T w := by
  simp only [longAcceptanceB, LongAcceptance, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Nat.succ_le_iff]
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **Rejection of long answers fails exactly when some witness works**: `RejectsLong` is a
universal statement over tuples, so its negation is a search for a tuple, and acceptance on
the tuple is a search for a budget, `Machine.runForD` returning the result of a run within
its budget (`Machine.runForD_eq_some_iff`). -/
theorem not_rejectsLong_iff_exists (n T : ℕ) :
    ¬ V.RejectsLong n T ↔ ∃ w, V.LongAcceptance n T w := by
  constructor
  · intro h
    simp only [RejectsLong, not_forall, not_not] at h
    obtain ⟨x, y, a, b, hlen, t, ht⟩ := h
    exact ⟨((x, y, a, b), t), hlen,
      (Machine.runForD_eq_some_iff ⟨encode true, t, le_rfl, ht⟩).2 ⟨t, ht⟩⟩
  · rintro ⟨⟨⟨x, y, a, b⟩, k⟩, hlen, hrun⟩ h
    exact h x y a b hlen (Machine.runs_of_runForD hrun)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
theorem computable_longInput :
    Computable fun z : LongZ α =>
      (encode (z.1.2, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2) : Data) := by
  have hw : Computable fun z : LongZ α => z.2.1 := Computable.fst.comp Computable.snd
  have hn : Computable fun z : LongZ α => z.1.2 := Computable.snd.comp Computable.fst
  have hx : Computable fun z : LongZ α => z.2.1.1 := Computable.fst.comp hw
  have hy : Computable fun z : LongZ α => z.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hw)
  have ha : Computable fun z : LongZ α => z.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hw))
  have hb : Computable fun z : LongZ α => z.2.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hw))
  have hebs : Computable fun l : BitStr => (encode l : Data) := Cost.primrec_encode_bitStr.to_comp
  exact Data.primrec_cons.to_comp.comp (Data.primrec_encode_nat.to_comp.comp hn)
    (Data.primrec_cons.to_comp.comp (hebs.comp hx)
      (Data.primrec_cons.to_comp.comp (hebs.comp hy)
        (Data.primrec_cons.to_comp.comp (hebs.comp ha) (hebs.comp hb))))
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
theorem computable_longRun (hV : ComputablyPresented V) :
    Computable fun z : LongZ α =>
      Machine.runForD (encode (V z.1.1).decider.prog)
        (encode (z.1.2, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2)) z.2.2 :=
  Computable.comp (f := fun q : (Data × Data) × ℕ => Machine.runForD q.1.1 q.1.2 q.2)
    (g := fun z : LongZ α =>
      (((encode (V z.1.1).decider.prog : Data),
        (encode (z.1.2, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2) : Data)), z.2.2))
    Machine.primrec_runForD.to_comp
    (((hV.deciderProg.comp (Computable.fst.comp Computable.fst)).pair computable_longInput).pair
      (Computable.snd.comp Computable.snd))
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
theorem computable_longRunB (hV : ComputablyPresented V) :
    Computable fun z : LongZ α =>
      decide (Machine.runForD (encode (V z.1.1).decider.prog)
        (encode (z.1.2, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2)) z.2.2
          = some (encode true)) :=
  -- the constant is taken at the `Primrec` level over `Option Data`: `Computable.const` over
  -- the search space itself is what made `rePred_not_isBounded` take eight minutes to elaborate
  Computable.comp (f := fun r : Option Data => decide (r = some (encode true)))
    (g := fun z : LongZ α =>
      Machine.runForD (encode (V z.1.1).decider.prog)
        (encode (z.1.2, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2)) z.2.2)
    (Cost.primrec_optionDataEqB.comp (Primrec.id.pair (Primrec.const (some (encode true))))).to_comp
    (computable_longRun hV)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
theorem computable_longLen {T : α → ℕ → ℕ}
    (hT : Computable fun q : α × ℕ => T q.1 q.2) :
    Computable fun z : LongZ α =>
      (decide (T z.1.1 z.1.2 + 1 ≤ z.2.1.2.2.1.length)
        || decide (T z.1.1 z.1.2 + 1 ≤ z.2.1.2.2.2.length)) := by
  have hw : Computable fun z : LongZ α => z.2.1 := Computable.fst.comp Computable.snd
  have ha : Computable fun z : LongZ α => z.2.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hw))
  have hb : Computable fun z : LongZ α => z.2.1.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hw))
  have hTq : Computable fun z : LongZ α => T z.1.1 z.1.2 + 1 :=
    Computable.comp (f := Nat.succ) (g := fun z : LongZ α => T z.1.1 z.1.2)
      Primrec.succ.to_comp (hT.comp Computable.fst)
  have hA : Computable fun z : LongZ α => decide (T z.1.1 z.1.2 + 1 ≤ z.2.1.2.2.1.length) :=
    Computable.comp (f := fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (g := fun z : LongZ α => (T z.1.1 z.1.2 + 1, z.2.1.2.2.1.length))
      Cost.primrec_natLeB.to_comp (hTq.pair (Primrec.list_length.to_comp.comp ha))
  have hB : Computable fun z : LongZ α => decide (T z.1.1 z.1.2 + 1 ≤ z.2.1.2.2.2.length) :=
    Computable.comp (f := fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (g := fun z : LongZ α => (T z.1.1 z.1.2 + 1, z.2.1.2.2.2.length))
      Cost.primrec_natLeB.to_comp (hTq.pair (Primrec.list_length.to_comp.comp hb))
  exact Primrec.or.to_comp.comp hA hB
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
theorem computable_longAcceptanceB (hV : ComputablyPresented V) {T : α → ℕ → ℕ}
    (hT : Computable fun q : α × ℕ => T q.1 q.2) :
    Computable fun z : LongZ α => (V z.1.1).longAcceptanceB z.1.2 (T z.1.1 z.1.2) z.2 := by
  unfold longAcceptanceB
  exact Primrec.and.to_comp.comp (computable_longLen hT) (computable_longRunB hV)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
/-- **The acceptance of a long answer is recursively enumerable** for a computably presented
family and a computable answer bound: `Verifier.not_rejectsLong_iff_exists` turns the failure
of `RejectsLong` into a search, `longAcceptanceB` runs the test — the length comparison and one
budgeted run of the decider — and `REPred.of_computable_exists` does the searching. This is the
third disjunct of `Verifier.not_inClassB_iff`. -/
theorem rePred_not_rejectsLong (hV : ComputablyPresented V) {T : α → ℕ → ℕ}
    (hT : Computable fun q : α × ℕ => T q.1 q.2) :
    REPred fun q : α × ℕ => ¬ (V q.1).RejectsLong q.2 (T q.1 q.2) := by
  refine (REPred.of_computable_exists (β := (BitStr × BitStr × BitStr × BitStr) × ℕ)
    (test := fun (q : α × ℕ) w => (V q.1).longAcceptanceB q.2 (T q.1 q.2) w)
    (computable_longAcceptanceB hV hT)).of_eq fun q => ?_
  rw [not_rejectsLong_iff_exists]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, ((V q.1).longAcceptanceB_iff q.2 (T q.1 q.2) w).1 hw⟩,
    fun ⟨w, hw⟩ => ⟨w, ((V q.1).longAcceptanceB_iff q.2 (T q.1 q.2) w).2 hw⟩⟩
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable {G : GapCompression} {U : UniversalMachine}
/-- **Obligation O3 from the tabulation of O2.** For a computably presented family of
verifiers and a computable tabulation whose game has the value of `𝒱_n` at every `n`-bounded
string, a closed program halts on `encode (x, n)` exactly off the class `B` at level `n` —
obligation O3 of the halting reduction, applied by `halting_reduction` through `exists_sem`.

The three disjuncts of `Verifier.not_inClassB_iff` are enumerated separately — the
boundedness violation by `Verifier.rePred_not_isBounded`, the acceptance of a long answer by
`Verifier.rePred_not_rejectsLong`, the value by `lem:value-lower-approx` on the tabulation —
and merged by dovetailing (`REPred.or`). -/
theorem exists_sem_of_tab (hV : Verifier.ComputablyPresented (Vof G U))
    (tab : BitStr → ℕ → GameData) (htab : Computable fun q : BitStr × ℕ => tab q.1 q.2)
    (hval : ∀ (x : BitStr) (n : ℕ), (Vof G U x).IsBounded n →
      quantumValue (tab x n).game = (Vof G U x).valStar n (ansBound G x n)) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ classB G U n := by
  have hre : REPred fun q : BitStr × ℕ => q.1 ∉ classB G U q.2 := by
    refine (REPred.or (REPred.or (Verifier.rePred_not_isBounded hV)
      (Verifier.rePred_not_rejectsLong hV (computable_ansBound G)))
      (rePred_lt_quantumValue_comp htab 1 2)).of_eq fun q => ?_
    rw [Halting.mem_classB_iff, Verifier.not_inClassB_iff]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    by_cases hb : (Vof G U q.1).IsBounded q.2
    · rw [hval q.1 q.2 hb, or_assoc]
    · simp [hb]
  exact Cost.exists_semidecider_prod_nat (p := fun x n => x ∉ classB G U n) hre
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable {G : GapCompression} {U : UniversalMachine}
/-- **The family `Vof` is computably presented.** All three fields, and all three are O2's:
the two programs by `computable_sampData`/`sampData_eq` and
`computable_decProgData`/`decProgData_eq`, and the third — the sampler's dimension,
*unconditionally* in the string and the level — by the re-budgeted `dimOf` read back by
`dimOf_eq`. That `dimOf_eq` carries no hypothesis is the whole point: `ComputablyPresented`
asks for the true dimension at every string and every level, including `n = 0` and `n = 1`,
and the budget `IsBounded n` supplies cannot reach those. What supplies it instead is
`GapCompression.sampler_time`, which holds for every parameter and every index. -/
theorem computablyPresented_Vof (G : GapCompression) (U : UniversalMachine) :
    Verifier.ComputablyPresented (Vof G U) where
  samplerProg := (computable_sampData G).of_eq fun x => sampData_eq G x
  deciderProg := (computable_decProgData G U).of_eq fun x => decProgData_eq G U x
  dim := (computable_dimOf_fst G).of_eq fun q => dimOf_eq G U q.1 q.2
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable {G : GapCompression} {U : UniversalMachine}
/-- **Obligation O3, with no hypotheses left.** Both arguments of `exists_sem_of_tab` are
discharged by O2: the computable presentation by the re-budgeted sampler runs, and `hval` —
the value equality at every `n`-bounded string, in both directions and with no synchronicity
— by the doubled question set of `Foundations/GameDouble.lean`.

This is the repair blueprint `lem:halting-semidecider` records as the first of three, and the
only one that changes nothing outside the tabulation: the two alternatives were to make
`Decider.wrap` reject unequal answers at equal questions, which changes what a string
*denotes* and so reopens `accOf_iff`, the classes and `thm:compression`; or to put
synchronicity into `classB`, which moves the cost into `compr_spec`, a field of the one
obligation still open. -/
theorem exists_sem (G : GapCompression) (U : UniversalMachine) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ classB G U n :=
  exists_sem_of_tab (computablyPresented_Vof G U) (tab G U) (tab_computable G U) (tab_value G U)
end MIPRE.Halting

namespace MIPRE.Verifier
open Cost
open Cost.Prog
/-- **The verifier a string denotes is `λ`-bounded**, at every level from some `n₀` on,
provided the sampler and the string's own decider have polynomially bounded cost and the
sampler's dimension is polynomially bounded. This is what inhabits `Verifier.IsBounded`. -/
theorem ofSamplerDecider_isBounded {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)
    (dec : Prog) (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → (ofSamplerDecider U S dec).IsBounded n :=
  (ofSamplerDecider U S dec).exists_isBounded hdim hS
    (wrapCore_hasPolyCost U S dec hS hdim hdec)
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
theorem decNo_runs (v : Data) : decNo.Runs v .nil 1 := Eval.nil _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
theorem decNo_hasPolyCost : decNo.HasPolyCost :=
  ⟨fun _ => 1, 0, PolyBounded.const 1, fun n d => ⟨.nil, 1, by simp, decNo_runs _⟩⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
/-- The rejecting decider never returns `encode true`. -/
theorem decNo_not_runs_true (v : Data) (t : ℕ) : ¬ decNo.Runs v (encode true) t := by
  intro h
  obtain ⟨he, -⟩ := (decNo_runs v).deterministic h
  exact absurd he.symm (by simp [encode_bool, Data.ofBool])
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
/-- The compressed sampler's cost is polynomially bounded: its time bound is
`bound (n + λ)` at the fixed degree `deg` (`GapCompression.sampler_time`). -/
theorem sampler_hasPolyCost (lam : ℕ) : (G.sampler lam).prog.HasPolyCost :=
  CL.Sampler.hasPolyCost_of_timeBound (T := fun n => G.bound.eval (n + lam)) (k := G.deg)
    (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)) fun n => G.sampler_time lam n
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
/-- Its dimension is polynomially bounded (`GapCompression.sampler_dim`). -/
theorem sampler_polyBounded_dim (lam : ℕ) : PolyBounded (G.sampler lam).dim :=
  (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)).mono (G.sampler_dim lam)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
/-- **O1, the rejecting side.** `yNo` lies in the class `B` at every level from some `n₀` on:
its verifier accepts nothing, hence is synchronous and has `val* = 0`, and it is `n`-bounded
above the threshold of `Verifier.ofSamplerDecider_isBounded`. -/
theorem yNo_mem : ∃ n₀, ∀ n, n₀ ≤ n → yNo ∈ classB G U n := by
  obtain ⟨n₀, hn₀⟩ := Verifier.ofSamplerDecider_isBounded U (G.sampler 0) decNo
    (sampler_hasPolyCost G 0) (sampler_polyBounded_dim G 0) decNo_hasPolyCost
  refine ⟨n₀, fun n hn => ?_⟩
  show (Vof G U yNo).InClassB n (ansBound G yNo n)
  rw [Vof_yNo]
  refine Verifier.inClassB_of_rejects_all _ (hn₀ n hn) fun x y a b hacc => ?_
  rw [Verifier.ofSamplerDecider_accepts] at hacc
  obtain ⟨-, -, t, ht⟩ := hacc
  exact decNo_not_runs_true _ _ ht
end MIPRE.Halting

namespace MIPRE.Halting.CompressorSpec
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
variable {G U} (S : CompressorSpec G U)
/-- The verifier of `x` frozen at `2n + 1` is `lam n`-bounded, from its `(2n + 1)`-boundedness
and the growth of `lam`. -/
theorem frozen_isBounded {x : BitStr} {n : ℕ} (hn : S.n₀ ≤ n)
    (hb : (Vof G U x).IsBounded (2 * n + 1)) :
    ((Vof G U x).freeze (2 * n + 1)).IsBounded (S.lam n) := by
  obtain ⟨h1, h2⟩ := S.lam_ge n hn
  obtain ⟨hdim, hS, hD⟩ := hb.1 (2 * n + 1) hb.two_le
  exact (Vof G U x).freeze_isBounded (2 * n + 1) (S.lam n) _ _ _ _ hS hD
    (hdim.trans (by omega)) h1 h1 (by omega) (by omega) (by have := hb.2; omega)
end MIPRE.Halting.CompressorSpec

namespace MIPRE.Halting.CompressorSpec
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
variable {G U} (S : CompressorSpec G U)
/-- The output's verifier has the compressed sampler at `lam n`, as the compression theorem's
output does. -/
theorem sampler_eq (c : Prog) (n : ℕ) (V : Prog × Prog) :
    (G.output V (S.lam n)).sampler = (Vof G U (S.compr (c, n))).sampler := by
  rw [G.output_sampler, Vof, Verifier.ofSamplerDeciderD_sampler, S.descLam_compr]
end MIPRE.Halting.CompressorSpec

namespace MIPRE.Halting.CompressorSpec
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
variable {G U} (S : CompressorSpec G U)
/-- The answer budget the output's class is read with is the one the compression theorem's
output is judged at. -/
theorem ansBound_compr (c : Prog) (n : ℕ) :
    ansBound G (S.compr (c, n)) n = G.bound.eval (n + S.lam n) := by
  rw [ansBound, S.descLam_compr]
end MIPRE.Halting.CompressorSpec

namespace MIPRE.Halting.CompressorSpec
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
variable {G U} (S : CompressorSpec G U)
/-- **The class transfer.** A compressor meeting the specification inhabits `Obligations`. -/
def toObligations : Obligations G U where
  n₀ := S.n₀
  compr := S.compr
  compr_spec := by
    intro c x n hn hc hsd hlen
    -- the objects: the described verifier, frozen; the compression theorem's output
    set V := Vof G U x with hV
    set W := G.output ((V.freeze (2 * n + 1)).sampler.prog, (V.freeze (2 * n + 1)).decider.prog)
      (S.lam n) with hW
    have hacc := S.accepts_compr c x n hn hc hsd hlen
    have hS : (Vof G U (S.compr (c, n))).sampler = W.sampler := (S.sampler_eq c n _).symm
    have hC₀ : G.C₀ ≤ n := S.C₀_le.trans hn
    have hans := S.ansBound_le x n hn hlen
    -- the output rejects long answers, as every compressed decider does
    have hrej : (Vof G U (S.compr (c, n))).RejectsLong n (ansBound G (S.compr (c, n)) n) := by
      intro x' y' a b hl h
      rw [S.ansBound_compr] at hl
      exact G.output_rejects_long _ (S.lam n) n x' y' a b hl ((hacc n x' y' a b).1 h)
    refine ⟨fun hA => ?_, fun hB => ?_⟩
    · obtain ⟨hb, -, hpcc⟩ := hA
      refine ⟨S.isBounded_compr c x n hn hc hsd hlen hb, hrej, ?_⟩
      -- raise the answer bound, freeze, compress, and read the result on the output's verifier
      have h1 : V.HasPerfectPCC (2 * n + 1) ((2 ^ n) ^ S.lam n) :=
        V.hasPerfectPCC_of_le hans hpcc
      have h2 : (V.freeze (2 * n + 1)).HasPerfectPCC (2 ^ n) ((2 ^ n) ^ S.lam n) :=
        (V.freeze_hasPerfectPCC (2 * n + 1) (2 ^ n) _).2 h1
      have h3 : W.HasPerfectPCC n (G.bound.eval (n + S.lam n)) :=
        G.completeness _ (S.lam n) n (S.frozen_isBounded hn hb) hC₀ h2
      rw [S.ansBound_compr]
      exact (Verifier.hasPerfectPCC_congr hS fun x' y' a b => (hacc n x' y' a b).symm).1 h3
    · obtain ⟨hb, hrejx, hval⟩ := hB
      refine ⟨S.isBounded_compr c x n hn hc hsd hlen hb, hrej, ?_⟩
      -- the described verifier rejects beyond its answer bound, so raising it keeps the value
      have h1 : V.valStar (2 * n + 1) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
        rw [V.valStar_eq_of_rejects hans hrejx]; exact hval
      have h2 : (V.freeze (2 * n + 1)).valStar (2 ^ n) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
        rw [V.freeze_valStar]; exact h1
      have h3 : W.valStar n (G.bound.eval (n + S.lam n)) ≤ 1 / 2 :=
        G.soundness _ (S.lam n) n (S.frozen_isBounded hn hb) hC₀ h2
      rw [S.ansBound_compr, ← Verifier.valStar_congr hS fun x' y' a b => (hacc n x' y' a b).symm]
      exact h3
end MIPRE.Halting.CompressorSpec

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- `2 ^ ·` is primitive recursive: the level at which the recursion of the criterion runs is
`2 ^ (K + 1 + esize e)`, and the reduction has to compute it. -/
theorem two_pow_iterate (n : ℕ) : (fun b : ℕ => 2 * b)^[n] 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n :=
  (Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂).of_eq fun n => two_pow_iterate n
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine)
/-- **The compressor's specification is inhabited.** -/
theorem exists_compressorSpec' : Nonempty (CompressorSpec G U) :=
  let ⟨S, _⟩ := exists_compressorSpec G U (comprPoly G U) fun _ _ => rfl
  ⟨S⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine)
/-- **Obligation O4 is discharged**: `Obligations G U` is inhabited. -/
theorem exists_obligations : Nonempty (Obligations G U) :=
  let ⟨S⟩ := exists_compressorSpec' G U
  ⟨S.toObligations⟩
end MIPRE.Halting

attribute [local irreducible] MIPRE.Halting.tab

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine)
include G U in
theorem _root_.solution :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame = 1 ∧ quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame ≤ 1 / 2 ∧ quantumValue (g pc).game ≤ 1 / 2) := by
  obtain ⟨O⟩ := exists_obligations G U
  obtain ⟨nY, hyes⟩ := yYes_mem G U
  obtain ⟨nN, hno⟩ := yNo_mem G U
  obtain ⟨sem, hsem_closed, hsem⟩ := exists_sem G U
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_levels
    (classA G U) (classB G U) (max (max nY nN) O.n₀)
    yYes (fun n hn => hyes n (by omega)) yNo (fun n hn => hno n (by omega))
    sem hsem_closed hsem O.compr (fun c x n hn => O.compr_spec c x n (by omega))
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  have hsize : Computable fun pc : Nat.Partrec.Code => esize (compile pc) :=
    Data.primrec_size.to_comp.comp hc
  have hlevel : Computable fun pc : Nat.Partrec.Code => 2 ^ (K + 1 + esize (compile pc)) :=
    (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const (K + 1)) Primrec.id)).to_comp.comp
      hsize
  refine ⟨fun pc => tab G U (g (compile pc)) (2 ^ (K + 1 + esize (compile pc))),
    (tab_computable G U).comp
      ((PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp).pair hlevel),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hg (compile pc)).2.1 ((hspec pc).2 hdom)
    refine ⟨gameValue_tab_eq_one G U _ _ hx.1 hx.2.2, ?_⟩
    rw [tab_value G U _ _ hx.1, (Vof G U _).valStar_eq_one_of_hasPerfectPCC hx.2.2]
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U _ _ hx.1
    exact ⟨Verifier.gameValue_toGame_le_of_valStar_le_doubled _ _ _ _ eX eA hμ hD hx.2.2,
      (tab_value G U _ _ hx.1).le.trans hx.2.2⟩
end MIPRE.Halting
