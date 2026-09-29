-- Prove2me | solution 1 for NgoFL.lattice_base_change_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T18:15:33.582968+00:00
-- url     : https://prove2.me/submissions/145762bf-b101-4bce-a7ed-5fdfadc25a02

import Mathlib
import Definitions.Def_NgoRootDatumIsogeny

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open NgoFL
open scoped TensorProduct

/-!
# Base change of a pair of lattices along a good base ring

Mathlib knows nothing about this situation.  The point is that the inclusion
`Λ₁ ∩ Λ₂ → Λ₁` becomes an isomorphism after tensoring with a ring in which the index
`[Λ₁ : Λ₁ ∩ Λ₂]` is invertible; the inverse is built by hand out of multiplication by the
index on the lattice side and by its inverse on the ring side.
-/

namespace NgoLatBC

variable {V : Type*} [AddCommGroup V] (L₁ L₂ : AddSubgroup V)

/-- Multiplication by the index carries `Λ₁` into `Λ₁ ∩ Λ₂`. -/
theorem nsmul_mem (b : L₁) : (latticeIndex L₁ L₂) • (b : V) ∈ L₁ ⊓ L₂ := by
  have h : (Nat.card (L₁ ⧸ (L₁ ⊓ L₂).addSubgroupOf L₁)) •
      (QuotientAddGroup.mk b : L₁ ⧸ (L₁ ⊓ L₂).addSubgroupOf L₁) = 0 := card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf] at h
  simpa [latticeIndex] using h

/-- Multiplication by the index, viewed as a map `Λ₁ → Λ₁ ∩ Λ₂`. -/
noncomputable def shrink : L₁ →ₗ[ℤ] (L₁ ⊓ L₂ : AddSubgroup V) where
  toFun b := ⟨(latticeIndex L₁ L₂) • (b : V), nsmul_mem L₁ L₂ b⟩
  map_add' b c := by
    apply Subtype.ext
    show (latticeIndex L₁ L₂) • ((b : V) + (c : V))
        = (latticeIndex L₁ L₂) • (b : V) + (latticeIndex L₁ L₂) • (c : V)
    rw [smul_add]
  map_smul' k b := by
    apply Subtype.ext
    show (latticeIndex L₁ L₂) • (k • (b : V)) = k • ((latticeIndex L₁ L₂) • (b : V))
    rw [smul_comm]

/-- The inclusion `Λ₁ ∩ Λ₂ → Λ₁` as a `ℤ`-linear map. -/
def incl : (L₁ ⊓ L₂ : AddSubgroup V) →ₗ[ℤ] L₁ :=
  (AddSubgroup.inclusion (inf_le_left : L₁ ⊓ L₂ ≤ L₁)).toIntLinearMap

theorem incl_shrink (b : L₁) : incl L₁ L₂ (shrink L₁ L₂ b) = (latticeIndex L₁ L₂) • b := by
  apply Subtype.ext; rfl

theorem shrink_incl (a : (L₁ ⊓ L₂ : AddSubgroup V)) :
    shrink L₁ L₂ (incl L₁ L₂ a) = (latticeIndex L₁ L₂) • a := by
  apply Subtype.ext; rfl

variable (O : Type*) [CommRing O]

/-- The candidate inverse of base change. -/
noncomputable def psi (u : Oˣ) :=
  TensorProduct.map (R := ℤ) (shrink L₁ L₂) (LinearMap.mulLeft ℤ (((u⁻¹ : Oˣ) : O)))

/-- The scalar cancellation that makes both composites the identity. -/
theorem key {M : Type*} [AddCommGroup M] (u : Oˣ)
    (hu : (u : O) = ((latticeIndex L₁ L₂ : ℕ) : O)) (x : M) (o : O) :
    ((latticeIndex L₁ L₂) • x) ⊗ₜ[ℤ] (((u⁻¹ : Oˣ) : O) * o) = x ⊗ₜ[ℤ] o := by
  have h1 : ((latticeIndex L₁ L₂ : ℕ) : ℤ) • x = (latticeIndex L₁ L₂) • x := by
    simp
  rw [← h1, TensorProduct.smul_tmul]
  congr 1
  rw [zsmul_eq_mul]
  push_cast
  rw [← hu, ← mul_assoc, u.mul_inv, one_mul]

theorem psi_rTensor (u : Oˣ) (hu : (u : O) = ((latticeIndex L₁ L₂ : ℕ) : O))
    (z : (L₁ ⊓ L₂ : AddSubgroup V) ⊗[ℤ] O) :
    psi L₁ L₂ O u (LinearMap.rTensor O (incl L₁ L₂) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a o =>
      rw [LinearMap.rTensor_tmul, psi, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
        shrink_incl]
      exact key L₁ L₂ O u hu a o
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem rTensor_psi (u : Oˣ) (hu : (u : O) = ((latticeIndex L₁ L₂ : ℕ) : O))
    (z : L₁ ⊗[ℤ] O) :
    LinearMap.rTensor O (incl L₁ L₂) (psi L₁ L₂ O u z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b o =>
      rw [psi, TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.rTensor_tmul,
        incl_shrink]
      exact key L₁ L₂ O u hu b o
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem base_change_bijective (h : IsGoodBase O L₁ L₂) :
    Function.Bijective
      (LinearMap.rTensor O
        (AddSubgroup.inclusion (inf_le_left : L₁ ⊓ L₂ ≤ L₁)).toIntLinearMap) := by
  obtain ⟨h1, -⟩ := h
  refine ⟨Function.LeftInverse.injective (g := psi L₁ L₂ O h1.unit) ?_,
    Function.RightInverse.surjective (g := psi L₁ L₂ O h1.unit) ?_⟩
  · exact psi_rTensor L₁ L₂ O h1.unit h1.unit_spec
  · exact rTensor_psi L₁ L₂ O h1.unit h1.unit_spec

end NgoLatBC

theorem solution {V : Type*} [AddCommGroup V] (L₁ L₂ : AddSubgroup V)
    (O : Type*) [CommRing O] (h : NgoFL.IsGoodBase O L₁ L₂) :
    Function.Bijective
      (LinearMap.rTensor O
        (AddSubgroup.inclusion (inf_le_left : L₁ ⊓ L₂ ≤ L₁)).toIntLinearMap) :=
  NgoLatBC.base_change_bijective L₁ L₂ O h
