-- Prove2me | solution 1 for MIPRE.AnswerReduction.sum_one_sub_value_copyStrategy_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:48:49.97797+00:00
-- url     : https://prove2.me/submissions/a09afc39-893b-4306-8506-a3c8585b16ee

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/SoundIsolate.lean (solution of MIPRE.AnswerReduction.sum_one_sub_value_copyStrategy_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundIsolate
import Theorems.Thm_MIPRE_AnswerReduction_cl_accepts_of_accepts
import Theorems.Thm_MIPRE_AnswerReduction_sum_copyFail_le
import Theorems.Thm_MIPRE_LIDT_CL_Regs_sum_sampleOf
import Theorems.Thm_MIPRE_TensorProductStrategy_succAt_adapt_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
theorem born_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b :=
  S.re_dotProduct_nonneg x y a b
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  have hsplit : ∑ x, ∑ y, G.μ x y * S.failAt x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * S.succAt x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by simp only [failAt]; ring
  rw [hsplit, G.μ_sum_one, value_eq_sum_succAt]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
/-- **The adapter does not lose acceptance.** If every tuple `G` accepts at `(qA x', qB y')` is
still accepted by `G'` at `(x', y')` after coarse-graining, the adapted strategy succeeds at
least as often there. -/
theorem succAt_le_succAt_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    S.succAt (qA x') (qB y') ≤ (S.adapt G' qA qB rA rB).succAt x' y' := by
  rw [succAt_adapt_eq]
  unfold succAt
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (S.born_nonneg _ _ a b)
  by_cases h : G.D (qA x') (qB y') a b = true
  · rw [if_pos h, if_pos (hD a b h)]
  · rw [if_neg h]
    split_ifs <;> norm_num
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
variable [DecidableEq A'] [DecidableEq B']
/-- Equivalently: the adapted strategy fails no more often. -/
theorem failAt_adapt_le (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    (S.adapt G' qA qB rA rB).failAt x' y' ≤ S.failAt (qA x') (qB y') := by
  simp only [failAt]
  linarith [succAt_le_succAt_adapt S G' qA qB rA rB x' y' hD]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool)
/-- Acceptance of the bit-string predicate is acceptance of `accepts` after the parse. -/
theorem accepts_of_typedPred {B : ℕ} {p q : Detyping.Question ArTy (Fin (dim V n P))}
    {a b : Verifier.Answers B} (h : typedPred V n P hk S S' check B p q a b = true) :
    ∃ u v, parse (fld P hk) p.1.2 a.1 = some u ∧ parse (fld P hk) q.1.2 b.1 = some v ∧
      accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v = true := by
  unfold typedPred at h
  split at h
  · rename_i u v hu hv
    exact ⟨u, v, hu, hv, h⟩
  · cases h
end
end MIPRE.AnswerReduction

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem canonLin_canonLin (S : Submodule F (Fin m → F)) (x : Fin m → F) :
    canonLin S (canonLin S x) = canonLin S x := by
  have h : canonLin S (x - canonLin S x) = 0 := by
    rw [← LinearMap.mem_ker, ker_canonLin]
    exact sub_canonLin_mem S x
  rw [map_sub, sub_eq_zero] at h
  exact h.symm
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem rep_rep (w u : Point F m) : rep w (rep w u) = rep w u := canonLin_canonLin _ u
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem zeroBelow_zeroBelow (i : Fin m) (v : Point F m) :
    zeroBelow i (zeroBelow i v) = zeroBelow i v := by
  funext k
  simp only [zeroBelow]
  split_ifs <;> rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
omit [DecidableEq F] in
/-- The sample's own questions are already canonical. -/
theorem recanon_question (sm : Sample F m) (τ : Ty) :
    recanon (hm := hm) (sm.question hm τ) = sm.question hm τ := by
  cases τ <;> simp [recanon, Sample.question, rep_rep, zeroBelow_zeroBelow]
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Regs ι m) (S : Sel F m hm)
omit [DecidableEq ι] [Fintype ι] in
theorem sampleOf_question (τ : Ty) (y : ι → F) :
    (R.sampleOf S τ y).question hm τ = recanon (hm := hm) (R.questionOf S τ y) := by
  cases τ <;> rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem ptOf_add (x y : ι → F) : R.ptOf (x + y) = R.ptOf x + R.ptOf y := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem dirOf_add (x y : ι → F) : R.dirOf (x + y) = R.dirOf x + R.dirOf y := rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem ptOf_single_coord (c : F) : R.ptOf (Pi.single R.coord c) = 0 := by
  funext i
  simp [ptOf, R.pt_ne_coord i]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem dirOf_single_coord (c : F) : R.dirOf (Pi.single R.coord c) = 0 := by
  funext j
  simp [dirOf, R.dir_ne_coord j]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
/-- **Reading a presented question back** gives the question. -/
theorem questionOf_embedQ (q : Question F n) : R.questionOf S q.ty (R.embedQ S q) = q := by
  cases q with
  | point u => simp [Question.ty, questionOf, embedQ]
  | aline u₀ s =>
    simp [Question.ty, questionOf, embedQ, ptOf_single_coord, ptOf_add, R.putPt_coord]
  | dline u₀ s v =>
    simp [Question.ty, questionOf, embedQ, ptOf_single_coord, dirOf_single_coord, ptOf_add,
      dirOf_add, R.putPt_coord, R.putDir_coord]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
omit [Fintype ι] in
/-- The sample read off a presented sample question gives the question back. -/
theorem sampleOf_embedQ (sm : Sample F n) (t : Ty) :
    (R.sampleOf S t (R.embedQ S (sm.question hn t))).question hn t = sm.question hn t := by
  have h := R.questionOf_embedQ S (sm.question hn t)
  rw [Sample.question_ty] at h
  rw [sampleOf_question, h, recanon_question]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)
/-- **Uniform content and a uniform pair of types give a uniform sample**: the sample the
registers carry at the first type, retyped to a pair of types, summed over both types and all
vectors, is every sample `q^{|ι| - (2n+1)}` times. -/
theorem sum_sampleOf_retype {M : Type*} [AddCommMonoid M] (g : Sample F n → M) :
    ∑ a : Ty, ∑ b : Ty, ∑ x : ι → F, g ((R.sampleOf S a x).retype a b)
      = (Fintype.card F ^ (Fintype.card ι - (2 * n + 1))) • ∑ sm : Sample F n, g sm := by
  have h a b : ∑ x : ι → F, g ((R.sampleOf S a x).retype a b) = _ :=
    R.sum_sampleOf S a (fun sm => g (sm.retype a b))
  simp_rw [h, ← Finset.smul_sum]
  congr 1
  rw [← (Sample.equiv F n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)
/-- The seeded test's distribution is the push-forward of the uniform sample. -/
theorem clGame_μ (x y : Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y =
      SampledGame.dist (fun sm : Sample F m => sm.question hm sm.tyA)
        (fun sm : Sample F m => sm.question hm sm.tyB) x y := by
  simp only [clGame, SampledGame.dist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun sm _ => ?_
  congr 1
  split_ifs <;> rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)
/-- **The seeded test's failure is the average failure over samples.** -/
theorem one_sub_value_clGame (T : TensorProductStrategy (clGame (d := d) (ldc := ldc) hm)) :
    1 - T.value = (∑ sm : Sample F m, T.failAt (sm.question hm sm.tyA) (sm.question hm sm.tyB))
      / Fintype.card (Sample F m) := by
  rw [T.one_sub_value_eq_sum_failAt]
  simp_rw [clGame_μ]
  exact SampledGame.sum_dist_mul _ _ T.failAt
end
end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
theorem pcpPart_append (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    pcpPart V n P hk (Fin.append x (pcpBits P hk w)) = w := by
  simp [pcpPart, pcpBits, rightPart_append]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
theorem oraclePart_append (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    oraclePart V n P (Fin.append x (pcpBits P hk w)) = x := by
  simp [oraclePart, leftPart_append]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
/-- **The per-seed strategy loses no acceptance**: on the question pair of a sample of the copy's
test, an answer pair the typed predicate accepts at the corresponding typed questions is read as
one the copy's test accepts, at a role pair where the copy is tested. -/
theorem copy_accepts {r : Role} {i : Fin 5} (hr : LDStep r i) (x₀ : Fin (V.sampler.dim n) → 𝔽₂)
    (sm : LIDT.CL.Sample (Fq P hk) P.m) {a b : Verifier.Answers B}
    (h : typedPred V n P hk S S' check B (arQ1 V n P hk S r i x₀ (sm.question hm sm.tyA))
      (arQ1 V n P hk S r i x₀ (sm.question hm sm.tyB)) a b = true) :
    LIDT.CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) (readAns1 P hk B i
      (sm.question hm sm.tyA) a) (readAns1 P hk B i (sm.question hm sm.tyB) b) = true := by
  obtain ⟨u, v, hu, hv, hacc⟩ := accepts_of_typedPred V n P hk S S' check h
  have hu' : parse (fld P hk) (i.castSucc, (sm.question hm sm.tyA).ty) a.1 = some u := hu
  have hv' : parse (fld P hk) (i.castSucc, (sm.question hm sm.tyB).ty) b.1 = some v := hv
  simp only [readAns1, hu', hv', Option.getD_some]
  simp only [decodeQ, arQ1, oraclePart_append, pcpPart_append] at hacc
  have hc := cl_accepts_of_accepts S S' check hr _ _ hacc
  simp only [q1, LIDT.CL.Sample.question_ty] at hc
  rw [LIDT.CL.Regs.sampleOf_embedQ, LIDT.CL.Regs.sampleOf_embedQ] at hc
  exact hc
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
/-- **The per-seed failure** is at most the average of `T`'s failures at the typed questions of
the copy's samples. -/
theorem one_sub_value_copyStrategy_le (T : TensorProductStrategy (typedGame V n P hk S S' check B))
    {r : Role} {i : Fin 5} (hr : LDStep r i) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    1 - (copyStrategy V n P hk S S' check B T r i y).value
      ≤ (∑ sm, copyFail V n P hk S S' check B T r i y sm)
        / Fintype.card (LIDT.CL.Sample (Fq P hk) P.m) := by
  rw [LIDT.CL.one_sub_value_clGame]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sm _ => ?_) (by positivity)
  exact TensorProductStrategy.failAt_adapt_le T _ _ _ _ _ _ _
    fun a b h => copy_accepts V n P hk S S' check B hr _ sm h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
theorem card_arTy_sq : Fintype.card (ArTy × ArTy) = 2916 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  rfl
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)
theorem _root_.solution
    (T : TensorProductStrategy (typedGame V n P hk S S' check B)) {r : Role} {i : Fin 5}
    (hr : LDStep r i) :
    ∑ x₀, (1 - (copyStrategy V n P hk S S' check B T r i
        ((roleFamily (V.sampler.cl n) r).eval x₀)).value)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (324 * (1 - T.value)) := by
  set K : ℝ := (Fintype.card (Fq P hk) : ℝ) ^ (Fintype.card (Coord P) - (2 * P.m + 1))
  set Sc : ℝ := (Fintype.card (LIDT.CL.Sample (Fq P hk) P.m) : ℝ)
  set Xc : ℝ := (Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) : ℝ)
  set Wc : ℝ := (Fintype.card (Coord P → Fq P hk) : ℝ)
  have hK : 9 * Wc = K * Sc := by
    have h := LIDT.CL.Regs.sum_sampleOf_retype (regs P i) S (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
    have h9 : Fintype.card LIDT.CL.Ty = 3 := rfl
    rw [h9] at h
    simp only [Wc, K, Sc]
    exact_mod_cast (by rw [← h]; ring : 9 * Fintype.card (Coord P → Fq P hk) = _)
  have hZ : (Fintype.card (Fin (dim V n P) → 𝔽₂) : ℝ) = Xc * Wc := by
    rw [← Fintype.card_congr (Fin.appendEquiv _ _), Fintype.card_prod,
      Fintype.card_congr (pcpBitsEquiv P hk).symm]
    push_cast
    rfl
  have hKpos : 0 < K := by positivity
  have hSpos : 0 < Sc := by
    simp only [Sc]
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(⟨.point, .point, 0, 0, 0⟩ : LIDT.CL.Sample (Fq P hk) P.m)⟩
  have h2 := sum_copyFail_le V n P hk S S' check B T r i
  rw [card_arTy_sq, hZ] at h2
  set L := roleFamily (V.sampler.cl n) r
  calc ∑ x₀, (1 - (copyStrategy V n P hk S S' check B T r i (L.eval x₀)).value)
      ≤ ∑ x₀, (∑ sm, copyFail V n P hk S S' check B T r i (L.eval x₀) sm) / Sc :=
        Finset.sum_le_sum fun x₀ _ => one_sub_value_copyStrategy_le V n P hk S S' check B T hr _
    _ = (∑ x₀, ∑ sm, copyFail V n P hk S S' check B T r i (L.eval x₀) sm) / Sc := by
        rw [Finset.sum_div]
    _ ≤ Xc * (324 * (1 - T.value)) := by
        rw [div_le_iff₀ hSpos]
        refine le_of_mul_le_mul_left ?_ hKpos
        refine h2.trans (le_of_eq ?_)
        push_cast
        linear_combination (324 * Xc * (1 - T.value)) * hK
end MIPRE.AnswerReduction
