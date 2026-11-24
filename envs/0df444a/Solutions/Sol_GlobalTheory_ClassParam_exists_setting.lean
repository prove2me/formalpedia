-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:40.374307+00:00
-- url     : https://prove2.me/submissions/fa421669-8e22-4683-b25b-279f9c3e037c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_leftMulMatrix_transfer
import Theorems.Thm_GlobalTheory_ClassParam_algebraMap_tmul
import Theorems.Thm_GlobalTheory_ClassParam_exists_basis_tensor
import Theorems.Thm_GlobalTheory_ClassParam_trace_tmul_one
import Theorems.Thm_GlobalTheory_ClassParam_exists_pow_basis
import Theorems.Thm_GlobalTheory_ClassParam_sigR_invol
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_of
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_root
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_starL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) :
    ∃ b : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k),
      HidaSetting (sigR (c : E →ₐ[F] E) k) (starLk k hP) (AdjoinRoot.root P ⊗ₜ[F] (1 : k)) b ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P ⊗ₜ[F] (1 : k))).charpoly
        = P.map (inclE (F := F) k) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  obtain ⟨b, hb, hch⟩ := exists_pow_basis hP
  obtain ⟨b', hb'⟩ := exists_basis_tensor (F := F) k b
  haveI := Module.Finite.of_basis b
  refine ⟨b', ⟨sigR_invol k _ hc, sigR_invol k _ (starL_starL hP hc), ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | tmul e t => simp [starLk, sigR, algebraMap_tmul, starL_of]
  · have : AdjoinRoot.root P * (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = 1 :=
      (alpha hP).mul_inv
    show _ * (starL hP (AdjoinRoot.root P) ⊗ₜ[F] (1 : k)) = 1
    rw [starL_root, Algebra.TensorProduct.tmul_mul_tmul, this, mul_one]
    rfl
  · intro i; rw [hb', hb, Algebra.TensorProduct.tmul_pow, one_pow]
  · have : Algebra.traceMatrix (E ⊗[F] k) b' = (Algebra.traceMatrix E b).map (inclE (F := F) k) := by
      ext i j
      simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply, hb',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_tmul_one k b]
      rfl
    rw [this]
    have h := (Algebra.discr_isUnit_of_basis E b).map (inclE (F := F) k)
    rw [Algebra.discr_def, RingHom.map_det] at h
    exact h
  · refine Eq.trans ?_ (congrArg (Polynomial.map (inclE (F := F) k)) hch)
    rw [← Matrix.charpoly_map]
    congr 1
    exact leftMulMatrix_transfer (inclE (F := F) k) (inclE (F := F) k) (fun _ => rfl) b b'
      (fun i => (hb' i).symm) _
end GlobalTheory.ClassParam
