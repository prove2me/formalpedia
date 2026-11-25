-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:22.402166+00:00
-- url     : https://prove2.me/submissions/8537d980-46b7-4d36-a789-a6a1b349fe6e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_conj_tri
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_herm
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_mul_self
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_posSemidef
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_tri
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_eq_one_of_posSemidef
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_eq_zero_of_unitary_blockTriangular
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_exists_cholesky
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_flip


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory.CompanionTheory.BmuIwa
theorem _root_.solution {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]
end GlobalTheory.CompanionTheory.BmuIwa
