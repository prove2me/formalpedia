-- Prove2me | solution 1 for MIPRE.SeededGame.sum_snorm_sq_joint_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:35.999992+00:00
-- url     : https://prove2.me/submissions/2d54dee9-a293-46ae-9d1c-28aafe836ed9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.sum_snorm_sq_joint_le);
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
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail
import Theorems.Thm_MIPRE_sum_snorm_sq_chain
import Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The master estimate.** A subtest that accepts only when two post-processings of the answers
agree bounds the cross-party deviation of the coarse-grained POVMs by twice its conditional
failure. Every item of `lem:qld-win` is an instance: name `f` and `g`, check the decider, and
read off the bound. -/
theorem xSqNorm_sum_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, xSqNorm ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ 2 * condFail G ψ MA MB x y := by
  refine le_trans (xSqNorm_sum_le_two_mul hψ _ _) ?_
  exact mul_le_mul_of_nonneg_left (one_sub_sum_bornProb_le_condFail f g hD) (by norm_num)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]
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

namespace MIPRE.TensorProductStrategy
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}
/-- The conditional failure of `povmValue`, read on the strategy's own measurements. -/
theorem condFail_eq_failAt (N : TensorProductStrategy G) (x : X) (y : Y) :
    condFail G N.ψ (fun x => N.PA.toPOVM x) (fun y => N.PB.toPOVM y) x y = N.failAt x y := rfl
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}
/-- **Accept implies agree**, for a bipartite strategy: if acceptance at `(x, y)` forces two
post-processings of the answers to agree, the cross-party deviation of the post-processed
measurements is at most twice the conditional failure there. -/
theorem sum_snorm_sq_fibre_le (N : TensorProductStrategy G) (x : X) (y : Y)
    {C : Type*} [Fintype C] [DecidableEq C] (f : A' → C) (g : B' → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, snorm N.ψ
        ((aOp (∑ a ∈ univ.filter fun a => f a = c, N.PA.M x a) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          - bOp (∑ b ∈ univ.filter fun b => g b = c, N.PB.M y b)) ^ 2
      ≤ 2 * N.failAt x y := by
  have h := xSqNorm_sum_le_condFail (G := G) (ψ := N.ψ) (MA := fun x => N.PA.toPOVM x)
    (MB := fun y => N.PB.toPOVM y) N.ψ_unit f g hD
  rw [N.condFail_eq_failAt] at h
  simpa only [xSqNorm_eq_snorm_sq, POVM.map_mats, ProjectiveMeasurement.toPOVM_mats_val] using h
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
theorem aliceView_of_oaccepts {z x : V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.alice, x) w u = true) : w.aliceView = u := by
  cases w <;> cases u <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.aliceView]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem bobView_of_oaccepts {z y : V} {w v : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.bob, y) w v = true) : w.bobView = v := by
  cases w <;> cases v <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.bobView]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem eq_of_oaccepts_self {p : Role × V} {u v : OAns A} (h : S.oaccepts p p u v = true) :
    u = v := by
  by_contra hne
  rw [S.oaccepts_eq_false_of_ne hne] at h
  exact Bool.false_ne_true h
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
theorem isPVM_oracleView (N : TensorProductStrategy S.oracular.toGame) (z : V)
    (f : OAns A → OAns A) : IsPVM (oracleView N z f) :=
  (N.PA.isPVM_at (Role.oracle, z)).fibre f
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
    ∑ o : OAns A × OAns A,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
              * bOp (N.PB.M (Role.bob, S.LB z) o.2)
          - aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2)) ^ 2
      ≤ 6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.bob, S.LB z)) := by
  have hchain := sum_snorm_sq_chain N.ψ (fun u => N.PA.M (Role.alice, S.LA z) u)
    (oracleView N z OAns.aliceView) (oracleView N z OAns.bobView)
    (fun u => N.PB.M (Role.alice, S.LA z) u) (fun v => N.PB.M (Role.bob, S.LB z) v)
    (N.PB.isPVM_at _) (isPVM_oracleView N z _)
  -- `(alice, alice)`: equal questions force equal answers
  have h1 := N.sum_snorm_sq_fibre_le (Role.alice, S.LA z) (Role.alice, S.LA z)
    (fun u : OAns A => u) (fun u => u) fun a b h => S.eq_of_oaccepts_self h
  -- `(oracle, alice)`: the oracle's Alice component matches the isolated Alice
  have h2 := N.sum_snorm_sq_fibre_le (Role.oracle, z) (Role.alice, S.LA z)
    OAns.aliceView (fun u => u) fun a b h => S.aliceView_of_oaccepts h
  -- `(oracle, bob)`: the oracle's Bob component matches the isolated Bob
  have h3 := N.sum_snorm_sq_fibre_le (Role.oracle, z) (Role.bob, S.LB z)
    OAns.bobView (fun u => u) fun a b h => S.bobView_of_oaccepts h
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton] at h1 h2 h3
  have e2 : ∀ c, (∑ a ∈ univ.filter fun a => a.aliceView = c, N.PA.M (Role.oracle, z) a)
      = oracleView N z OAns.aliceView c := fun c => rfl
  have e3 : ∀ c, (∑ a ∈ univ.filter fun a => a.bobView = c, N.PA.M (Role.oracle, z) a)
      = oracleView N z OAns.bobView c := fun c => rfl
  simp only [e2, e3] at h2 h3
  linarith
end MIPRE.SeededGame
