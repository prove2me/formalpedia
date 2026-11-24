-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DenSum.dI_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:23.171612+00:00
-- url     : https://prove2.me/submissions/e3045cd0-dc45-4916-b62a-bc5ee89b8b48

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_mem_dI

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.DenSum
theorem _root_.solution (b : F) : dI b ≠ ⊥ := by
  intro h
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) b
  have hmem : (s : 𝓞 F) ∈ dI b := mem_dI.mpr ⟨a, by rw [mul_comm]; exact hs.symm⟩
  rw [h, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.coe_ne_zero s hmem
end GlobalTheory.CompanionTheory.SW.DenSum
