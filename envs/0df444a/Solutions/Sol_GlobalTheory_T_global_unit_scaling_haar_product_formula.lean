-- Prove2me | solution 1 for GlobalTheory.T.global_unit_scaling_haar_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:38:42.647572+00:00
-- url     : https://prove2.me/submissions/d6862ddc-e0dd-4b7e-b105-dec27093d38a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_unitProd_scalar


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | exact GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar <;> assumption)
end _root_.GlobalTheory.T
