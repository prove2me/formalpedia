-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.isOpen_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:45.106282+00:00
-- url     : https://prove2.me/submissions/2aaf20d3-998a-4788-b917-0087aa1fe0e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
namespace GlobalTheory.CompanionTheory.QLTop
theorem _root_.solution (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen ((𝒪[F] : Subring F) : Set F) := by
  refine AddSubgroup.isOpen_of_mem_nhds (𝒪[F] : Subring F).toAddSubgroup (g := 0) ?_
  refine (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mpr ⟨1, one_ne_zero, fun x hx => ?_⟩
  exact (Valuation.mem_integer_iff _ _).mpr (le_of_lt hx)
end GlobalTheory.CompanionTheory.QLTop
