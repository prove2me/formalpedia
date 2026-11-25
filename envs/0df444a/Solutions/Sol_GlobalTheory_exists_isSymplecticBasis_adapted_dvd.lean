-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasis_adapted_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:17.084365+00:00
-- url     : https://prove2.me/submissions/39193561-8852-4db9-be9b-38edad272f90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_adapted_mod
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
open TensorProduct
variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {B : LinearMap.BilinForm ℤ Λ}
namespace GlobalTheory
theorem _root_.solution (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank ℤ Λ = 2 * g) {N : ℕ} (hN : N ≠ 0) {P Q : Submodule ℤ Λ}
    (hNP : ∀ x, (N : ℤ) • x ∈ P) (hNQ : ∀ x, (N : ℤ) • x ∈ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, (N : ℤ) ∣ B x y) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, (N : ℤ) ∣ B x y)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (Fin g ⊕ Fin g) ℤ Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inr i)) ∧
      ∀ x, x ∈ Q ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inl i) := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  have key : ∀ {T : Submodule ℤ Λ}, (∀ x, (N : ℤ) • x ∈ T) →
      RingHom.ker (Int.castRingHom (ZMod N)) • ⊤ ≤ T := fun hT =>
    Submodule.smul_le.2 fun r hr x _ => by
      obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r N).1 hr
      rw [mul_smul]
      exact hT _
  simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using
    hb.exists_adapted_mod (f := Int.castRingHom (ZMod N)) (ZMod.ringHom_surjective _) hB
      (key hNP) (key hNQ)
      (by simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using hP)
      (by simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using hQ) hPQ
end GlobalTheory
