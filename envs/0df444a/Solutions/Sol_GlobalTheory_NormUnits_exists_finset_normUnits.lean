-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_finset_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:27.929392+00:00
-- url     : https://prove2.me/submissions/4d422cb2-7c13-4a8a-a4ae-0414249a37cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnits
import Theorems.Thm_GlobalTheory_NormUnits_fg_quot_intUnits
import Theorems.Thm_GlobalTheory_NormUnits_exists_finset_sq_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ,
    (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  intro K B hP
  let N : Subgroup B.Aˣ := B.T ⊔ intUnits K.O B.A
  have hFG : Group.FG (B.Aˣ ⧸ N) :=
    haveI := fg_quot_intUnits K B hP
    Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right)
      (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)
  obtain ⟨F, hF⟩ := exists_finset_sq_mem N hFG
  refine ⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩
  let su : B.Aˣ := Units.map (B.σ : B.A →* B.A) u
  have hsu : (su : B.A) = B.σ u := rfl
  have ht : u * su⁻¹ ∈ B.T := by
    show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1
    have h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1 := by
      have : B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rwa [hsu, B.σ_σ] at this
    calc ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A)
        = (B.σ ((su⁻¹ : B.Aˣ) : B.A) * u) * ((su : B.A) * ((su⁻¹ : B.Aˣ) : B.A)) := by
          simp only [Units.val_mul, map_mul]; rw [hsu]; ring
      _ = 1 := by rw [h1, Units.mul_inv, one_mul]
  have hsq : u ^ 2 ∈ N := by
    have : u ^ 2 = (u * su⁻¹) * w := by
      ext; rw [Units.val_mul, hwu, ← hsu]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul]
      calc (u : B.A) ^ 2 = (u : B.A) * u * (((su⁻¹ : B.Aˣ) : B.A) * su) := by rw [Units.inv_mul, mul_one, sq]
        _ = _ := by ring
    rw [this]; exact N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)
  obtain ⟨f, hfF, hf⟩ := hF u hsq
  obtain ⟨t, htT, z, hz, htz⟩ := Subgroup.mem_sup.mp hf
  refine ⟨f, hfF, t, htT, ?_⟩
  have : u * f⁻¹ * t⁻¹ = z := by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]; exact hz
end GlobalTheory.NormUnits
