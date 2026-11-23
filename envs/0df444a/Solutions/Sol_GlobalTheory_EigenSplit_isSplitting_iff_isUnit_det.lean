-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isSplitting_iff_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.823275+00:00
-- url     : https://prove2.me/submissions/fed07c94-976d-4be4-9929-ba430b1da143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
variable [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Fintype ι] (σ : ι → O →+* R) (b : Module.Basis ι ℤ O) :
    IsSplitting σ ↔ IsUnit (Matrix.of fun i j => σ i (b j)).det := by
  have key : LinearMap.toMatrix (Algebra.TensorProduct.basis R b) (Pi.basisFun R ι)
      (splitMap σ).toLinearMap = Matrix.of fun i j => σ i (b j) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  constructor
  · intro h
    rw [← key]
    exact LinearEquiv.isUnit_det (splitEquiv h).toLinearEquiv _ _
  · intro h
    rw [← key] at h
    exact (LinearEquiv.ofIsUnitDet h).bijective
end GlobalTheory.EigenSplit
