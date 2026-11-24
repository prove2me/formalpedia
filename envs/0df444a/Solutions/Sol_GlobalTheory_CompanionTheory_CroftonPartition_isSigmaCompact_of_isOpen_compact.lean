-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CroftonPartition.isSigmaCompact_of_isOpen_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:19.885225+00:00
-- url     : https://prove2.me/submissions/b81c11ef-5a6d-4112-be0f-ad9ddbc1ea45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SigmaCompactDisjointRefinement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CroftonPartition
namespace GlobalTheory.CompanionTheory.CroftonPartition
theorem _root_.solution {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
end GlobalTheory.CompanionTheory.CroftonPartition
