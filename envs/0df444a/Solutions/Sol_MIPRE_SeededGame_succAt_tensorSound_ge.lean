-- Prove2me | solution 1 for MIPRE.SeededGame.succAt_tensorSound_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:48.897766+00:00
-- url     : https://prove2.me/submissions/57d8c830-1483-44bf-9c4d-377f480caa77

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.succAt_tensorSound_ge);
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
import Theorems.Thm_MIPRE_SeededGame_succAt_oracle_le
import Theorems.Thm_MIPRE_SeededGame_sum_snorm_sq_joint_le
import Theorems.Thm_MIPRE_TensorProductStrategy_succAt_adapt_eq
import Theorems.Thm_MIPRE_TensorProductStrategy_sum_born
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_snorm_sq_ge_of_close

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
theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform, Matrix.one_mulVec, ← norm_evec_sq, hv, one_pow]
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
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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
/-- **The two factors commute.** -/
theorem aOp_mul_bOp (X : Matrix HA HA ℂ) (Y : Matrix HB HB ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ) * bOp Y = bOp Y * aOp X := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
/-- A projective family stays projective on the product space. -/
theorem IsPVM.aOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dA dA ℂ} (h : IsPVM Q) :
    IsPVM fun i => (aOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [aOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← aOp_mul, h.idem]
  sum_eq_one := by rw [← aOp_sum, h.sum_eq_one, aOp_one]
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
variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]
/-- A projective measurement has total squared mass one on a unit vector. -/
theorem sum_snorm_sq_eq_one_of_isPVM [DecidableEq N] {v : N → ℂ} (hv : ‖evec v‖ = 1)
    {M : ι → Matrix N N ℂ} (hM : IsPVM M) : ∑ i, snorm v (M i) ^ 2 = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [snorm_sq_eq_qform, hM.isSelfAdjoint i, hM.idem i],
    ← qform_sum, hM.sum_eq_one, qform_one v hv]
end
end MIPRE

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
/-- For projections `X`, `Y`, the squared mass of `X ⊗ Y` is its quadratic form. -/
theorem snorm_sq_aOp_mul_bOp_of_proj (ψ : HA × HB → ℂ) {X : Matrix HA HA ℂ} {Y : Matrix HB HB ℂ}
    (hX : Xᴴ = X) (hXX : X * X = X) (hY : Yᴴ = Y) (hYY : Y * Y = Y) :
    snorm ψ ((aOp X : Matrix (HA × HB) (HA × HB) ℂ) * bOp Y) ^ 2
      = qform ψ ((aOp X : Matrix (HA × HB) (HA × HB) ℂ) * bOp Y) := by
  rw [snorm_sq_eq_qform]
  congr 1
  rw [Matrix.conjTranspose_mul, bOp_conjTranspose, aOp_conjTranspose, hX, hY]
  calc (bOp Y : Matrix (HA × HB) (HA × HB) ℂ) * aOp X * (aOp X * bOp Y)
      = aOp X * bOp Y * (aOp X * bOp Y) := by rw [← aOp_mul_bOp]
    _ = aOp X * (aOp X * bOp Y * bOp Y) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bOp Y), ← aOp_mul_bOp]
    _ = aOp X * bOp Y := by
        rw [Matrix.mul_assoc (aOp X), ← bOp_mul, hYY, ← Matrix.mul_assoc, ← aOp_mul, hXX]
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
/-- The Born probability is the squared mass of `A^x_a ⊗ B^y_b`, the operators being
projections. -/
theorem snorm_sq_eq_born (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') (b : B') :
    snorm N.ψ ((aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
        * bOp (N.PB.M y b)) ^ 2 = N.born x y a b := by
  rw [snorm_sq_aOp_mul_bOp_of_proj N.ψ ((N.PA.isPVM_at x).isSelfAdjoint a) ((N.PA.isPVM_at x).idem a)
    ((N.PB.isPVM_at y).isSelfAdjoint b) ((N.PB.isPVM_at y).idem b), N.born_eq_qform]
end
end MIPRE.TensorProductStrategy

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

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A] in
/-- The product of the two isolated measurements has total mass one. -/
theorem sum_snorm_sq_isolated (N : TensorProductStrategy S.oracular.toGame) (x y : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, x) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M (Role.bob, y) o.2)) ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [N.snorm_sq_eq_born]
  exact N.sum_born _ _
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
/-- The oracle's joint marginal has total mass one. -/
theorem sum_snorm_sq_oracleJoint (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ (aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 = 1 :=
  sum_snorm_sq_eq_one_of_isPVM (norm_evec_eq_one_of_unit N.ψ_unit) (isPVM_oracleJoint N z).aOp
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
/-- **The extracted strategy wins at least the accepted isolated answer pairs.** -/
theorem succAt_tensorSound_ge_sum (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o ∈ (S.accPairs z).map singlePairEmb,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M (Role.bob, S.LB z) o.2)) ^ 2
      ≤ (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  rw [tensorSound, TensorProductStrategy.succAt_adapt_eq, ← Fintype.sum_prod_type']
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ
    ((S.accPairs z).map singlePairEmb)) fun o _ _ =>
      mul_nonneg (by split_ifs <;> norm_num) (N.born_nonneg _ _ _ _))
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ho
  have hD : S.D (S.LA z) (S.LB z) p.1 p.2 = true := (Finset.mem_filter.mp hp).2
  rw [N.snorm_sq_eq_born]
  simp only [singlePairEmb_apply, OAns.singlePart, toGame_D, hD, if_true, one_mul]
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
theorem _root_.solution (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    1 - N.failAt (Role.oracle, z) (Role.oracle, z)
        - 2 * √(6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  have hclose := sum_snorm_sq_ge_of_close N.ψ
    (fun o : OAns A × OAns A => (aOp (N.PA.M (Role.alice, S.LA z) o.1) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) * bOp (N.PB.M (Role.bob, S.LB z) o.2))
    (fun o => aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2))
    (le_of_eq (sum_snorm_sq_isolated N _ _)) (le_of_eq (sum_snorm_sq_oracleJoint N z))
    ((S.accPairs z).map singlePairEmb)
  have hroot := Real.sqrt_le_sqrt (sum_snorm_sq_joint_le N z)
  have hsucc := succAt_oracle_le N z
  have hwin := succAt_tensorSound_ge_sum N z
  have hfail : N.failAt (Role.oracle, z) (Role.oracle, z)
      = 1 - N.succAt (Role.oracle, z) (Role.oracle, z) := rfl
  linarith
end MIPRE.SeededGame
