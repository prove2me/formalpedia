-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitProdAlg.family_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:13.035324+00:00
-- url     : https://prove2.me/submissions/09cf24ae-8945-4e3d-9c55-af223ebc7b49

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_mulSupport_finite

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
theorem _root_.solution {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by
  intro hv
  have h2 := h.2
  rw [finprod_eq_zero c v hv (mulSupport_finite h)] at h2
  simp at h2
end GlobalTheory.CompanionTheory.SW.UnitProdAlg
