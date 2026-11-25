-- Prove2me | solution 1 for GlobalTheory.T.unit_product_closure_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:53.108046+00:00
-- url     : https://prove2.me/submissions/ef2a3297-d53e-49d7-baf5-9e7f69b15c9c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosurePropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0) (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e → a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧ IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧ IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧ (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | exact GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | (intros; apply GlobalTheory.CompanionTheory.SW.UnitProdAlg.main <;> assumption)
end _root_.GlobalTheory.T
