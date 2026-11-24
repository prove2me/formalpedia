-- Prove2me | solution 1 for GlobalTheory.det_points_ne_zero_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:02.464781+00:00
-- url     : https://prove2.me/submissions/69cae2a4-646c-4983-91e3-fdfbaee4c389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_exists_algEquiv_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
variable [Module.Finite R S]
variable [DecidableEq ι]
omit [Module.Free R S] [Module.Finite R S]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[R] E)) (b : Basis ι R S) :
    (Matrix.of fun i j ↦ P j (b i)).det ≠ 0 := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  have h := (Pi.basisFun E ι).isUnit_det ((Algebra.TensorProduct.basis E b).map e.toLinearEquiv)
  rw [Basis.det_apply, ← Matrix.det_transpose] at h
  convert h.ne_zero using 2
  ext i j
  simp [Basis.toMatrix_apply, Algebra.TensorProduct.basis_apply, he]
end GlobalTheory
