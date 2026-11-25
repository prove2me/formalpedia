-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.adapted_dec_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:03.286139+00:00
-- url     : https://prove2.me/submissions/2994157b-5b65-432d-8d5b-a7c2b8b91fb1

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_adapted_dec_one
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_conj_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_conj_mul
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_herm
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_mul_self
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
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by
  have hA := h.mul_self
  have hAH := h.herm
  obtain ⟨k, B, hk, hkA, hBA, hg, hB⟩ := adapted_dec_one h _ (conj_mem hA hAH hx)
  set A := dp p 0 c
  have hBl := conj_mul hA hBA
  have hk' : k * kᴴ = 1 := mul_eq_one_comm.1 hk
  refine ⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA
  · let _ : Invertible B := invertibleOfLeftInverse B _ hBl
    rw [← inv_eq_left_inv hBl]
    exact blockTriangular_inv_of_blockTriangular hB
  · rw [conjTranspose_conjTranspose]; exact hk'
  · have h1 : k * B * x = 1 := by rw [← hg]; exact conj_mul hA hx
    calc x = (A * Bᴴ * A * B) * x := by rw [hBl, Matrix.one_mul]
      _ = A * Bᴴ * A * ((kᴴ * k) * B * x) := by rw [hk, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = A * Bᴴ * A * kᴴ * (k * B * x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
end GlobalTheory.CompanionTheory.BmuIwa
