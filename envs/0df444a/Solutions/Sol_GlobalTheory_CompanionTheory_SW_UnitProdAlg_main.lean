-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitProdAlg.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:20.86404+00:00
-- url     : https://prove2.me/submissions/37e5f8f5-905c-462a-bf01-f5db7ac3c400

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_mulSupport_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_map_hom
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_family_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e h k
  refine ⟨ne_zero h, family_ne_zero h, mul h k, inv h, ?_, map_hom sqrtHom h,
    fun n => map_hom (powMonoidHom n) h, (mulSupport_finite h).toFinset, fun S hS => ?_⟩
  · simpa only [div_eq_mul_inv] using mul h (inv k)
  · have hsub : Function.mulSupport c ⊆ (S : Set _) := by
      intro v hv
      exact hS ((mulSupport_finite h).mem_toFinset.2 hv)
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (hsub hne)
    · rw [← finprod_eq_prod_of_mulSupport_subset c hsub]
      exact h.2
end GlobalTheory.CompanionTheory.SW.UnitProdAlg
