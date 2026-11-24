-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.preserves_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:07.980678+00:00
-- url     : https://prove2.me/submissions/1de1c744-a3ca-4297-87b4-a41a1fa0a869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox
namespace GlobalTheory.UnRep.WeakApprox
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * σ (y b)) ↔
      gᵀ * G * g.map σ = G := by
  have h1 : ∀ x y : Fin n → R, ∑ a, ∑ b, x a * G a b * σ (y b) = x ⬝ᵥ (G *ᵥ (σ ∘ y)) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : ∀ x y : Fin n → R, (g *ᵥ x) ⬝ᵥ (G *ᵥ (σ ∘ (g *ᵥ y))) =
      x ⬝ᵥ ((gᵀ * G * g.map σ) *ᵥ (σ ∘ y)) := by
    intro x y
    have : σ ∘ (g *ᵥ y) = g.map σ *ᵥ (σ ∘ y) := by
      funext i
      exact RingHom.map_mulVec σ g y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
      Matrix.vecMul_transpose]
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single a 1) (Pi.single b 1)
    have e : σ ∘ (Pi.single b 1 : Fin n → R) = Pi.single b 1 := by
      funext i
      by_cases hi : i = b
      · subst hi; simp
      · simp [hi]
    simpa [e] using this
  · intro h x y
    rw [h]
end GlobalTheory.UnRep.WeakApprox
