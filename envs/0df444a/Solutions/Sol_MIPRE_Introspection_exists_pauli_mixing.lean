-- Prove2me | solution 1 for MIPRE.Introspection.exists_pauli_mixing
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:47:58.560266+00:00
-- url     : https://prove2.me/submissions/89da07df-8db0-474b-8365-806019f649c7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliMixing.lean (solution of MIPRE.Introspection.exists_pauli_mixing);
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
import Theorems.Thm_MIPRE_Introspection_block_retention_dist_avg
import Theorems.Thm_MIPRE_Introspection_fine_commutator_parseval
import Theorems.Thm_MIPRE_Introspection_linear_measurement_fourier
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_twirl_blocks
import Theorems.Thm_MIPRE_Introspection_pauli_twirl_dist_le
import Theorems.Thm_MIPRE_Introspection_sum_norm_linearFourier_sq
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_Weyl_epr_unit
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_stateVec_epr
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

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
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVecB_sum {ι : Type*} (ψ : dA × dB → ℂ) (t : Finset ι) (f : ι → Matrix dB dB ℂ) :
    stateVecB ψ (∑ i ∈ t, f i) = ∑ i ∈ t, stateVecB ψ (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [stateVecB]
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, stateVecB, stateVecB, stateVecB,
        Matrix.kronecker_add, Matrix.add_mulVec]
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
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
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
theorem stateSqNorm_sub_comm (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateSqNorm ψ (M - N) = stateSqNorm ψ (N - M) := by
  rw [stateSqNorm, stateSqNorm, stateNorm, stateNorm, norm_stateVec_eq_snorm,
    norm_stateVec_eq_snorm, aOp_sub, aOp_sub, snorm_sub_comm]
end
end MIPRE

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The same for the spectral projectors of either family, which are built from the operators by
a real Fourier average and are therefore symmetric too. -/
theorem stateVec_epr_proj {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (e : n → F) :
    stateVec (epr (F := F) (n := n)) (proj w e) = stateVecB epr (proj w e) := by
  rw [stateVec_epr]
  congr 1
  rw [proj_def, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_smul, hw a]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- **Coarse-grained eigenbasis projectors transport across the maximally entangled state**,
exactly: each spectral projector does (`stateVec_epr_proj`) and the level-set projector is a sum of
them. -/
theorem stateVec_epr_synOf {C : Type*} [DecidableEq C] (hw : ∀ a, (w a)ᵀ = w a)
    (φ : (n → F) → C) (o : C) :
    stateVec (epr (F := F) (n := n)) (synOf w φ o) = stateVecB epr (synOf w φ o) := by
  rw [synOf, stateVec_sum, stateVecB_sum]
  exact Finset.sum_congr rfl fun e _ => stateVec_epr_proj hw e
end
end MIPRE.Weyl

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem synOf_eq_zero_of_not_mem_range
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (a : Fin n → F) (ha : a ∉ L.range) :
    synOf w L a = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact (ha ⟨e, (Finset.mem_filter.mp he).2⟩).elim
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
/-- The readout/observable Parseval identity after any linear action on vectors. -/
theorem linear_measurement_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (f : Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] (N → ℂ)) :
    (∑ y : Fin n → F, ‖evec (f (synOf w L y))‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (f (w v.1))‖ ^ 2) := by
  have h := sum_norm_linearFourier_sq L (fun y => f (synOf w L y))
    (fun y hy => by rw [synOf_eq_zero_of_not_mem_range w L y hy, map_zero])
  have hv (v : CL.perp L.ker) : f (w v.1) =
      ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • f (synOf w L y) := by
    rw [linear_measurement_fourier w L v.1 v.2, map_sum]
    simp only [map_smul]
  simpa only [hv] using h.symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
variable {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]
/-- `lem:W`: the two commutator errors agree exactly, without a dimension factor. -/
theorem linear_measurement_commutator_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf w L y) - aOp (synOf w L y) * M)) =
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
      ∑ v : CL.perp L.ker, stateSqNorm ψ (M * aOp (w v.1) - aOp (w v.1) * M) :=
  linear_measurement_parseval w L (commutatorAction ψ M)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix
open scoped ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
set_option maxHeartbeats 800000 in
open Kronecker in
/-- A Pauli-twirled POVM is a linear-map readout followed by an actual ancillary POVM. -/
theorem linear_twirl_povm {A : Type*} [Fintype A]
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (P : POVM A ((Fin n → F) × H)) :
    ∃ Q : (Fin n → F) → POVM A H, ∀ a,
      averageX L.ker (dephaseZ (H := H) (P.mats a)) =
        ∑ y : Fin n → F, synOf wZ L y ⊗ₖ ((Q y).mats a : Matrix H H ℂ) := by
  refine ⟨fun y => blockPOVM L.ker P (linearPreimage L y), fun a => ?_⟩
  simp only [blockPOVM_mats]
  exact linear_twirl_blocks (H := H) L (P.mats a)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Exact consistency survives adjoining any bipartite ancillary state. -/
theorem mirror_expVec (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (P : Matrix V V ℂ) (Q : Matrix W W ℂ) (h : stateVec ψ P = stateVecB ψ Q) :
    stateVec (expVec ψ ξ) (aOp P : Matrix (V × H) _ ℂ) =
      stateVecB (expVec ψ ξ) (aOp Q : Matrix (W × K) _ ℂ) := by
  have hbase := congrArg WithLp.ofLp h
  change (P ⊗ₖ (1 : Matrix W W ℂ)) *ᵥ ψ = ((1 : Matrix V V ℂ) ⊗ₖ Q) *ᵥ ψ at hbase
  unfold stateVec stateVecB aOp
  congr 1
  rw [show (1 : Matrix (W × K) (W × K) ℂ) =
      (1 : Matrix W W ℂ) ⊗ₖ (1 : Matrix K K ℂ) from Matrix.one_kronecker_one.symm,
    show (1 : Matrix (V × H) (V × H) ℂ) =
      (1 : Matrix V V ℂ) ⊗ₖ (1 : Matrix H H ℂ) from Matrix.one_kronecker_one.symm,
    mulVec_kron_kron_expVec, mulVec_kron_kron_expVec, hbase]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}
/-- The expanded EPR state is normalized whenever its ancillary state is. -/
theorem eprWithAux_norm (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    ‖evec (eprWithAux (F := F) (n := n) ξ)‖ = 1 := by
  have he : ‖evec (epr (F := F) (n := Fin n))‖ = 1 := by
    have hs := norm_evec_sq (epr (F := F) (n := Fin n))
    rw [epr_unit, Complex.one_re] at hs
    nlinarith [norm_nonneg (evec (epr (F := F) (n := Fin n)))]
  rw [eprWithAux, norm_evec_expVec, he, hξ, one_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}
/-- A coarse-grained `Z` readout has the same exact mirror. -/
theorem eprWithAux_readout_mirror (ξ : H × K → ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    aOp (aOp (synOf wZ L y) : Matrix ((Fin n → F) × H) _ ℂ) *ᵥ eprWithAux ξ =
      bOp (aOp (synOf wZ L y) : Matrix ((Fin n → F) × K) _ ℂ) *ᵥ eprWithAux ξ := by
  exact congrArg WithLp.ofLp
    (mirror_expVec (epr (F := F) (n := Fin n)) ξ _ _ (stateVec_epr_synOf wZ_transpose L y))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
/-- The `L`-perpendicular readout transfers to the uniform Pauli error on `ker L`. -/
theorem kernel_commutator_parseval
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf wX (CL.lperp L) y) - aOp (synOf wX (CL.lperp L) y) * M)) =
    (Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker,
      stateSqNorm ψ (M * aOp (wX v.1) - aOp (wX v.1) * M) := by
  have h := linear_measurement_commutator_parseval wX (CL.lperp L) ψ M
  let e : CL.perp (CL.lperp L).ker ≃ L.ker :=
    { toFun v := ⟨v.1, by simpa only [CL.ker_lperp, CL.perp_perp] using v.2⟩
      invFun v := ⟨v.1, by simpa only [CL.ker_lperp, CL.perp_perp] using v.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  refine h.trans ?_
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
/-- The twirl error controlled directly by the two projective-readout commutator errors. -/
theorem pauli_twirl_readout_dist_le (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
    (∑ a, stateSqNorm (eprWithAux ξ)
      (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
      4 * (∑ a, ∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
        ((M.mats a).val * aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
          aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * (M.mats a).val)) +
      4 * (∑ a, ∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
        ((M.mats a).val * aOp (synOf wX (CL.lperp L) y) -
          aOp (synOf wX (CL.lperp L) y) * (M.mats a).val)) := by
  simp_rw [fine_commutator_parseval, kernel_commutator_parseval, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a v : _ =>
    stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)),
    Finset.sum_comm (f := fun a (v : L.ker) =>
    stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val))]
  exact pauli_twirl_dist_le L ξ M
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]
theorem _root_.solution (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H))
    (hM : IsPVM (fun p => (M.mats p).val)) :
    ∃ Q : (Fin n → F) → POVM A H,
      (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        ((M.mats p).val - synOf wZ L p.1 ⊗ₖ ((Q p.1).mats p.2).val)) ≤
      2 * mixingError L ξ M + 4 * Real.sqrt (mixingError L ξ M) := by
  obtain ⟨Q, hQ⟩ := linear_twirl_povm L M
  have hdist := pauli_twirl_readout_dist_le L ξ M
  have hswap : (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
      ((M.mats p).val - ∑ z, synOf wZ L z ⊗ₖ ((Q z).mats p).val)) =
      ∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        (averageX L.ker (dephaseZ (M.mats p).val) - (M.mats p).val) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [← hQ p, stateSqNorm_sub_comm]
  have hclose : 2 * (∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
      ((∑ a, (M.mats (y, a)).val) - aOp (synOf wZ L y))) +
      2 * (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        ((M.mats p).val - ∑ z, synOf wZ L z ⊗ₖ ((Q z).mats p).val)) ≤ mixingError L ξ M := by
    rw [hswap]
    unfold mixingError readoutMarginalError readoutCommutatorError
    linarith
  have h := block_retention_dist_avg (fun _ : Unit => (1 : ℝ)) (by simp) (by simp)
    (eprWithAux ξ) (eprWithAux_norm ξ hξ) (fun _ p => (M.mats p).val) (fun _ => hM)
    (fun _ => synOf wZ L) (fun _ => linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (fun _ => Q) (fun _ y => (aOp (synOf wZ L y) : Matrix ((Fin n → F) × K) _ ℂ))
    (fun _ => (linear_measurement_isPVM wZ isWeylFamily_wZ L).aOp)
    (fun _ y => eprWithAux_readout_mirror ξ L y)
    (by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using hclose)
  refine ⟨fun y => (Q y).map Prod.snd, ?_⟩
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h
end MIPRE.Introspection
