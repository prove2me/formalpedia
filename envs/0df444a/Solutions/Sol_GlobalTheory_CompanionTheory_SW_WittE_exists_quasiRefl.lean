-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.exists_quasiRefl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:34.134843+00:00
-- url     : https://prove2.me/submissions/cb24893b-d631-4a27-83df-fd2483d9a517

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal

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
theorem _root_.solution (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (x y : V) (hxy : B x x = B y y) (h0 : B (x - y) x ≠ 0) :
    ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ γ x = y ∧ ∀ z, B (x - y) z = 0 → γ z = z := by
  set v := x - y with hv
  set a := B v x with ha
  have hsa : σ a = B x v := hB _ _
  have hsa0 : σ a ≠ 0 := (map_ne_zero σ).2 h0
  have hvv : B v v = a + σ a := by
    rw [hsa, ha, hv]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]
    ring
  have hγ : ∀ z, (LinearMap.id - (a⁻¹ • B v).smulRight v : V →ₗ[E] V) z
      = z - (a⁻¹ * B v z) • v := by
    intro z
    simp
  refine ⟨LinearMap.id - (a⁻¹ • B v).smulRight v, ?_, ?_, ?_⟩
  · intro z w
    have hzv : B z v = σ (B v z) := (hB v z).symm
    rw [hγ, hγ]
    simp only [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, map_mul, map_inv₀, hvv, hzv, RingHom.id_apply]
    field_simp
    ring
  · rw [hγ, ← ha, inv_mul_cancel₀ h0, one_smul, hv, sub_sub_cancel]
  · intro z hz
    rw [hγ, hz]
    simp
end GlobalTheory.CompanionTheory.SW.WittE
