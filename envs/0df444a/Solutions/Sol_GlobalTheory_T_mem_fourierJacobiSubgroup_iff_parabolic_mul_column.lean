-- Prove2me | solution 1 for GlobalTheory.T.mem_fourierJacobiSubgroup_iff_parabolic_mul_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:25.542378+00:00
-- url     : https://prove2.me/submissions/8fe6bb9d-4933-4eac-8dee-c59ebf970ba7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumnStatement
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_mem_RFJ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  first | exact @GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | exact GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff <;> assumption)
end _root_.GlobalTheory.T
