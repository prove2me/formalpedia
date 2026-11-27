-- Prove2me | solution 1 for GlobalTheory.T.sigma_compact_disjoint_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:29.541794+00:00
-- url     : https://prove2.me/submissions/30d51f21-f73b-42fc-914c-32153966a8ac

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SigmaCompactDisjointRefinement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SigmaCompactDisjointRefinementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_exists_sigmaCompact_partition


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) → (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X), Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧ ∀ t, IsSigmaCompact (A t) := by
  first | exact @GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | exact GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | (intros; apply GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition <;> assumption)
end _root_.GlobalTheory.T
