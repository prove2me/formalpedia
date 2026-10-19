-- Prove2me | solution 1 for MIPRE.Introspection.dilated_pvm_distance
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:24:36.389981+00:00
-- url     : https://prove2.me/submissions/20ec3f94-1304-495b-aaa5-fd8f5bb4046b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingInductionDilation.lean (solution of MIPRE.Introspection.dilated_pvm_distance);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Theorems.Thm_MIPRE_Introspection_abs_sum_qform_mul_le
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed

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
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
/-- Pulling a Born-rule expectation back along a linear map `W` conjugates the observable:
`⟨Wv| M |Wv⟩ = ⟨v| Wᴴ M W |v⟩`. With `W` an isometry and `M` a projection this is how a
dilated projective measurement compresses back to the POVM it came from. -/
theorem dotProduct_mulVec_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix κ ι ℂ) (M : Matrix κ κ ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (M *ᵥ (W *ᵥ v)) = star v ⬝ᵥ ((Wᴴ * (M * W)) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- The same, on the other side of the isometry. -/
theorem ancillaEmbed_conjTranspose_mul_kron_one (a₀ : A) (M : Matrix dA dA ℂ) :
    (ancillaEmbed dA a₀)ᴴ * (M ⊗ₖ (1 : Matrix A A ℂ)) = M * (ancillaEmbed dA a₀)ᴴ := by
  have h := congrArg Matrix.conjTranspose (kron_one_mul_ancillaEmbed a₀ (Mᴴ))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- **Compressing a product whose left factor has an inert ancilla.** -/
theorem compress_kron_one_mul (a₀ : A) (M : Matrix dA dA ℂ) (Y : Matrix (dA × A) (dA × A) ℂ) :
    (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * Y * ancillaEmbed dA a₀)
      = M * ((ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀)) := by
  calc (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * Y * ancillaEmbed dA a₀)
      = (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * (Y * ancillaEmbed dA a₀)) := by
        rw [Matrix.mul_assoc (M ⊗ₖ (1 : Matrix A A ℂ))]
    _ = (ancillaEmbed dA a₀)ᴴ * (M ⊗ₖ (1 : Matrix A A ℂ)) * (Y * ancillaEmbed dA a₀) := by
        rw [Matrix.mul_assoc ((ancillaEmbed dA a₀)ᴴ) (M ⊗ₖ (1 : Matrix A A ℂ))
          (Y * ancillaEmbed dA a₀)]
    _ = M * (ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀) := by
        rw [ancillaEmbed_conjTranspose_mul_kron_one]
    _ = M * ((ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀)) := by
        rw [Matrix.mul_assoc M ((ancillaEmbed dA a₀)ᴴ) (Y * ancillaEmbed dA a₀)]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- The conjugation identity: a quadratic form on the extended state is the quadratic form of the
**compressed** operator on the original one. -/
theorem qform_extVecA (ψ : dA × dB → ℂ) (a₀ : A) (M : Matrix (dA × A) (dA × A) ℂ) :
    qform (extVecA ψ a₀) (aOp M : Matrix ((dA × A) × dB) _ ℂ)
      = qform ψ (aOp ((ancillaEmbed dA a₀)ᴴ * (M * ancillaEmbed dA a₀))) := by
  rw [qform, qform, extVecA, dotProduct_mulVec_conj]
  congr 2
  rw [aOp, aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
/-- An operator with an inert ancilla compresses to itself. -/
theorem compress_aOp (b₀ : Bnc) (N : Matrix dB dB ℂ) :
    (ancillaEmbed dB b₀)ᴴ * ((aOp N : Matrix (dB × Bnc) _ ℂ) * ancillaEmbed dB b₀) = N := by
  rw [aOp, kron_one_mul_ancillaEmbed,
    ← Matrix.mul_assoc ((ancillaEmbed dB b₀)ᴴ) (ancillaEmbed dB b₀) N, ancillaEmbed_isometry,
    Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem dotProduct_star_comm (u w : N → ℂ) : star u ⬝ᵥ w = star (star w ⬝ᵥ u) := by
  rw [dotProduct, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul']
  simp [Pi.star_apply, mul_comm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The quadratic form does not see the adjoint: it is a real part, and the adjoint conjugates. -/
theorem qform_conjTranspose (v : N → ℂ) (M : Matrix N N ℂ) : qform v (Mᴴ) = qform v M := by
  have h0 := star_mulVec_dotProduct M (1 : Matrix N N ℂ) v
  rw [Matrix.mul_one, Matrix.one_mulVec] at h0
  rw [qform, qform, ← h0, dotProduct_star_comm (M *ᵥ v) v, RCLike.star_def, Complex.conj_re,
    dotProduct_star_comm v (M *ᵥ v), RCLike.star_def, Complex.conj_re]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
theorem _root_.solution (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (M R : A → Matrix H H ℂ) (P : A → Matrix (H × T) (H × T) ℂ)
    (hM : IsPVM M) (hP : IsPVM P)
    (hk : ∀ a, (ancillaEmbed H a₀)ᴴ * (P a * ancillaEmbed H a₀) = R a)
    {δ : ℝ} (hd : ∑ a, stateSqNorm ψ (M a - R a) ≤ δ) :
    (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) ≤ 2 * Real.sqrt δ := by
  have hsumR : ∑ a, R a = 1 := by
    simp_rw [← hk]
    rw [← Matrix.mul_sum, ← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul,
      ancillaEmbed_isometry]
  have hexp a : stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a) =
      qform ψ (aOp (M a)) + qform ψ (aOp (R a)) -
        2 * qform ψ (aOp (M a * R a)) := by
    have hsym : qform (extVecA ψ a₀) (aOp (P a * aOp (M a))) =
        qform (extVecA ψ a₀) (aOp (aOp (M a) * P a)) := by
      rw [← qform_conjTranspose _ (aOp (aOp (M a) * P a)),
        aOp_conjTranspose, Matrix.conjTranspose_mul, hP.isSelfAdjoint,
        aOp_conjTranspose, hM.isSelfAdjoint]
    rw [stateSqNorm_eq_qform, Matrix.conjTranspose_sub, aOp_conjTranspose,
      hM.isSelfAdjoint, hP.isSelfAdjoint, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, ← aOp_mul, hM.idem, hP.idem,
      aOp_sub, aOp_sub, aOp_sub, qform_sub, qform_sub, qform_sub, hsym]
    have hc : (ancillaEmbed H a₀)ᴴ * (aOp (M a) * P a * ancillaEmbed H a₀) = M a * R a := by
      rw [aOp, compress_kron_one_mul, hk]
    simp only [qform_extVecA, compress_aOp, hk, hc]
    ring
  have hsum : (∑ a, stateSqNorm (extVecA ψ a₀) (aOp (M a) - P a)) =
      2 * ∑ a, qform ψ (aOp (M a * (M a - R a))) := by
    simp_rw [hexp, Matrix.mul_sub, hM.idem, aOp_sub, qform_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← qform_sum, ← qform_sum, ← aOp_sum,
      ← aOp_sum, hM.sum_eq_one, hsumR]
    ring
  have hmass : (∑ a, snorm ψ (aOp (M a) : Matrix (H × K) _ ℂ) ^ 2) = 1 := by
    simp_rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hM.isSelfAdjoint, hM.idem]
    rw [← qform_sum, ← aOp_sum, hM.sum_eq_one, aOp_one, qform_one ψ hψ]
  have hcs := abs_sum_qform_mul_le ψ univ
    (fun a => (aOp (M a) : Matrix (H × K) _ ℂ))
    (fun a => (aOp (M a - R a) : Matrix (H × K) _ ℂ))
    (fun a => by rw [aOp_conjTranspose, hM.isSelfAdjoint])
  rw [hmass, Real.sqrt_one, one_mul] at hcs
  simp only [← aOp_mul] at hcs
  have hδ : (∑ a, snorm ψ (aOp (M a - R a) : Matrix (H × K) _ ℂ) ^ 2) ≤ δ := hd
  rw [hsum]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hcs.trans (Real.sqrt_le_sqrt hδ))) (by norm_num)
end MIPRE.Introspection
