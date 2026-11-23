-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:09.053997+00:00
-- url     : https://prove2.me/submissions/21bce0ce-cb72-48b5-a6ed-c7a326d25035

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_latR_eq_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) (y : InfinitePlace F → ℝ) :
    y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F)) := by
  rw [latR_eq_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
end GlobalTheory.CompanionTheory.SW.FD
