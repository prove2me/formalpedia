-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LenFib.exists_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:40.602122+00:00
-- url     : https://prove2.me/submissions/89fe2ec1-98f6-42eb-89a6-707b86d47213

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsFibreFamilyLength

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LenFib
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.LenFib
theorem _root_.solution [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by
  obtain ⟨K, hK, hcK, hKU⟩ := exists_compact_subset hU hc₀
  obtain ⟨f, hf1, -, hfs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨f, f.continuous, hfs, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc
end GlobalTheory.CompanionTheory.SW.LenFib
