-- Prove2me | solution 1 for GlobalTheory.EigenSplit.det_sq_eq_discr_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:46:34.870792+00:00
-- url     : https://prove2.me/submissions/96854ab8-47df-4937-bb99-b3e8e450987d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_card_eq_of_basis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {L : Type*} [Field L] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => φ i (b j)).det ^ 2 = (NumberField.discr E : L) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have := card_eq_of_basis b
    rw [Fintype.card_eq_zero] at this
    exact absurd this Module.finrank_pos.ne
  have : CharZero L := charZero_of_injective_ringHom (φ i₀).injective
  let A := AlgebraicClosure L
  let ψ : ι → (E →ₐ[ℚ] A) := fun i => ((algebraMap L A).comp (φ i)).toRatAlgHom
  have hψ : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card, AlgHom.card, card_eq_of_basis b]
    exact ⟨fun i j hij => hφ (RingHom.ext fun x =>
      (algebraMap L A).injective (DFunLike.congr_fun hij x)), rfl⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ A
    (fun j => (b j : E)) (Equiv.ofBijective ψ hψ)
  have h2 : Algebra.discr ℚ (fun j => (b j : E)) = (NumberField.discr E : ℚ) := by
    have := Algebra.discr_localizationLocalization ℤ (Rₘ := ℚ) (nonZeroDivisors ℤ) E b
    rw [NumberField.discr_eq_discr] at this
    rw [eq_intCast] at this
    convert this using 2
    ext j
    simp
  apply (algebraMap L A).injective
  rw [h2] at h1
  rw [map_pow, RingHom.map_det, map_intCast, ← Matrix.det_transpose]
  rw [map_intCast] at h1
  rw [h1]
  congr 2
end GlobalTheory.EigenSplit
