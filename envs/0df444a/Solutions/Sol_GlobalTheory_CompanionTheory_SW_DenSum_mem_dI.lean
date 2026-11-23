-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DenSum.mem_dI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:58.812783+00:00
-- url     : https://prove2.me/submissions/524bd7e5-4c18-41f1-bb72-0493df0fec42

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable

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
theorem _root_.solution {b : F} {x : 𝓞 F} : x ∈ dI b ↔ ∃ t : 𝓞 F, (t : F) = (x : F) * b := by
  simp only [dI, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
    Algebra.smul_def]
end GlobalTheory.CompanionTheory.SW.DenSum
