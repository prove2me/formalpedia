-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Plus.pow_max_max_le_max_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:09.466554+00:00
-- url     : https://prove2.me/submissions/38d29b6c-b3cd-46ad-988a-c494dbc48f82

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Plus
variable {t}
namespace GroundTheory.PAdicHodge.NormTower.Plus
theorem _root_.solution {a b c : ℝ} (n : ℕ) :
    (max (max a b) c) ^ n ≤ max (max (a ^ n) (b ^ n)) (c ^ n) := by
  rcases max_choice (max a b) c with h | h
  · rw [h]
    rcases max_choice a b with h' | h'
    · rw [h']; exact le_max_of_le_left (le_max_left _ _)
    · rw [h']; exact le_max_of_le_left (le_max_right _ _)
  · rw [h]; exact le_max_right _ _
end GroundTheory.PAdicHodge.NormTower.Plus
