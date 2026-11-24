-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.exists_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:18.438697+00:00
-- url     : https://prove2.me/submissions/0c929dc6-30d1-4eaa-8d7c-9c0d9952d42c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution (B : V →ₛₗ[σ] V →ₗ[E] E) (hB : ∀ x y, σ (B x y) = B y x)
    (h2 : (2 : E) ≠ 0) {n : ℕ} (X : Fin n → V) (hX : ¬ ∀ a b, B (X a) (X b) = 0) :
    ∃ c : Fin n → E, B (lin X c) (lin X c) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hX
  intro a b
  by_contra hs
  have hu : B (X a) (X a) = 0 := by simpa [lin_single] using hc (Pi.single a (1 : E))
  have hv : B (X b) (X b) = 0 := by simpa [lin_single] using hc (Pi.single b (1 : E))
  set s := B (X a) (X b) with hsdef
  have hba : B (X b) (X a) = σ s := (hB _ _).symm
  have h := hc (Pi.single a (1 : E) + s⁻¹ • Pi.single b (1 : E))
  rw [lin_add, lin_smul, lin_single, lin_single] at h
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, hu, hv, hba, ← hsdef, map_inv₀, RingHom.id_apply] at h
  have hσs : σ s ≠ 0 := (map_ne_zero σ).2 hs
  simp only [mul_zero, add_zero, zero_add, inv_mul_cancel₀ hs, inv_mul_cancel₀ hσs] at h
  exact h2 (by linear_combination h)
end GlobalTheory.CompanionTheory.SW.WittE
