-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.isOpen_isCompact_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:45.787236+00:00
-- url     : https://prove2.me/submissions/96e702c7-72f8-4289-aec3-5b2871d82ced

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.QLTop
theorem _root_.solution : IsOpen ((𝒪[F] : Subring F) : Set F) ∧ IsCompact ((𝒪[F] : Subring F) : Set F) := by
  refine ⟨?_, ?_⟩
  · exact Valuation.isOpen_valuationSubring (valuation F)
  · exact isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[F])
end GlobalTheory.CompanionTheory.QLTop
