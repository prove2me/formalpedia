-- Prove2me | solution 1 for MIPRE.SeededGame.succAt_oracle_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:20.22263+00:00
-- url     : https://prove2.me/submissions/bae0fcd7-155d-4c7f-bc9d-59565c7323cb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.succAt_oracle_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
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
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_OAns_sum_eq
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem aOp_mul (X Y : Matrix HA HA ℂ) :
    aOp (X * Y) = (aOp X : Matrix (HA × HB) _ ℂ) * aOp Y := by
  rw [aOp, aOp, aOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]
end
end MIPRE

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

namespace MIPRE
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
/-- **The product of two fibre sums is the fibre sum over the intersection**: distinct outcomes of
a projective measurement are orthogonal. -/
theorem IsPVM.sum_mul_sum {P : Λ → Matrix n n ℂ} (hP : IsPVM P) (s t : Finset Λ) :
    (∑ a ∈ s, P a) * (∑ b ∈ t, P b) = ∑ a ∈ s ∩ t, P a := by
  rw [Finset.sum_mul_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ t
  · rw [if_pos ha, Finset.sum_eq_single_of_mem a ha fun b _ hba => hP.orthogonal (Ne.symm hba),
      hP.idem a]
  · rw [if_neg ha]
    exact Finset.sum_eq_zero fun b hb => hP.orthogonal fun hab => ha (hab ▸ hb)
end
end MIPRE

namespace MIPRE
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
/-- **A projective measurement, coarse-grained, is projective.** -/
theorem IsPVM.fibre {P : Λ → Matrix n n ℂ} (hP : IsPVM P) {C : Type*} [Fintype C] [DecidableEq C]
    (f : Λ → C) : IsPVM fun c => ∑ a ∈ univ.filter fun a => f a = c, P a where
  isSelfAdjoint c := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => hP.isSelfAdjoint a
  idem c := by rw [hP.sum_mul_sum, Finset.inter_self]
  sum_eq_one := by
    rw [Finset.sum_fiberwise_of_maps_to (fun a _ => mem_univ (f a))]
    exact hP.sum_eq_one
end
end MIPRE

namespace MIPRE
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
/-- The operators of a projective measurement at one question form a PVM. -/
theorem ProjectiveMeasurement.isPVM_at {X A : Type*} [Fintype A] {n : Type*} [Fintype n]
    [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) :
    IsPVM (P.M x) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact P.selfAdjoint x a
  idem a := P.projective x a
  sum_eq_one := P.normalized x
end
end MIPRE

namespace MIPRE
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
/-- For a projection `X`, the squared mass of `X ⊗ Id` is its quadratic form. -/
theorem snorm_sq_aOp (ψ : HA × HB → ℂ) {X : Matrix HA HA ℂ} (hX : Xᴴ = X) (hXX : X * X = X) :
    snorm ψ (aOp X : Matrix (HA × HB) (HA × HB) ℂ) ^ 2
      = qform ψ (aOp X : Matrix (HA × HB) (HA × HB) ℂ) := by
  rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hX, hXX]
end
end MIPRE

namespace MIPRE.TensorProductStrategy
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}
/-- The Born probability, as the quadratic form of `A^x_a ⊗ B^y_b` on the joint space. -/
theorem born_eq_qform (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') (b : B') :
    N.born x y a b
      = qform N.ψ ((aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M y b)) :=
  bornProb_eq_qform N.ψ (N.PA.M x a) (N.PB.M y b)
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}
/-- Summing out the second player's outcome leaves the first player's marginal. -/
theorem sum_born_right (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') :
    ∑ b, N.born x y a b
      = qform N.ψ (aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
  simp_rw [N.born_eq_qform]
  rw [← qform_sum, ← Finset.mul_sum, ← bOp_sum, N.PB.normalized y, bOp_one, Matrix.mul_one]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem oracleGood_of_oaccepts {z : V} {q : Role × V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) q w u = true) : S.oracleGood z w = true := by
  cases w <;> simp_all [oaccepts, shapeOk, gameCheck, oracleGood]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A] in
/-- The two component marginals multiply to the joint marginal. -/
theorem oracleView_mul (N : TensorProductStrategy S.oracular.toGame) (z : V) (u v : OAns A) :
    oracleView N z OAns.aliceView u * oracleView N z OAns.bobView v
      = ∑ w ∈ univ.filter fun w => (w.aliceView, w.bobView) = (u, v),
          N.PA.M (Role.oracle, z) w := by
  rw [oracleView, oracleView, (N.PA.isPVM_at _).sum_mul_sum, ← Finset.filter_and]
  refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
  simp [Prod.ext_iff]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A] in
/-- **The oracle's joint marginal is a projective measurement.** -/
theorem isPVM_oracleJoint (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    IsPVM fun o : OAns A × OAns A =>
      oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2 := by
  have h := (N.PA.isPVM_at (Role.oracle, z)).fibre fun w : OAns A => (w.aliceView, w.bobView)
  convert h using 1
  funext o
  exact oracleView_mul N z o.1 o.2
end
end MIPRE.SeededGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A] in
theorem _root_.solution (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ o ∈ (S.accPairs z).map singlePairEmb,
          snorm N.ψ (aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 := by
  have hproj : ∀ w, snorm N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2
        = qform N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := fun w =>
    snorm_sq_aOp N.ψ ((N.PA.isPVM_at _).isSelfAdjoint w) ((N.PA.isPVM_at _).idem w)
  -- the oracle's acceptance is at most the mass of its good answers
  have hgood : N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ u, (if S.oracleGood z u then 1 else 0) *
          qform N.ψ (aOp (N.PA.M (Role.oracle, z) u) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
    unfold TensorProductStrategy.succAt
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← N.sum_born_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (N.born_nonneg _ _ _ _)
    by_cases h : S.oracular.toGame.D (Role.oracle, z) (Role.oracle, z) u w = true
    · rw [if_pos h, if_pos (S.oracleGood_of_oaccepts h)]
    · rw [if_neg h]
      split_ifs <;> norm_num
  -- the good answers are the accepted pairs
  have hpairs : ∑ u, (if S.oracleGood z u then 1 else 0) *
        qform N.ψ (aOp (N.PA.M (Role.oracle, z) u) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
      = ∑ p ∈ S.accPairs z, qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
    rw [OAns.sum_eq, accPairs, Finset.sum_filter]
    have hsingle : ∑ a : A, (if S.oracleGood z (OAns.single a) = true then (1 : ℝ) else 0) *
        qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.single a)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        show (if false = true then (1 : ℝ) else 0) * _ = 0
        simp
    rw [hsingle, add_zero]
    refine Finset.sum_congr rfl fun p _ => ?_
    show (if S.D (S.LA z) (S.LB z) p.1 p.2 = true then (1 : ℝ) else 0) * _ = _
    split_ifs <;> simp
  -- and each accepted pair lies in its fibre of the joint marginal
  have hfibre : ∀ p ∈ S.accPairs z,
      qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
        ≤ snorm N.ψ (aOp (oracleView N z OAns.aliceView (OAns.single p.1)
            * oracleView N z OAns.bobView (OAns.single p.2)) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 := by
    intro p _
    have hJ := isPVM_oracleJoint N z
    rw [snorm_sq_aOp N.ψ (hJ.isSelfAdjoint (OAns.single p.1, OAns.single p.2))
      (hJ.idem (OAns.single p.1, OAns.single p.2)), oracleView_mul, aOp_sum, qform_sum]
    refine Finset.single_le_sum (f := fun w => qform N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)) (fun w _ => ?_) ?_
    · rw [← hproj w]
      exact sq_nonneg _
    · simp [OAns.aliceView, OAns.bobView]
  calc N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ p ∈ S.accPairs z, qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := hgood.trans (le_of_eq hpairs)
    _ ≤ _ := by
        rw [Finset.sum_map]
        exact Finset.sum_le_sum hfibre
end MIPRE.SeededGame
