-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_neg
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:28.609894+00:00
-- url     : https://prove2.me/submissions/c709b040-361f-496a-8c6a-2f3c7009dae4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
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
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]
theorem _root_.solution (a b : ℤ → K) : cmul a (-b) = -cmul a b := by
  first
    | (funext n
       simp [GroundTheory.PAdicHodge.Laurent.cmul, tsum_neg, mul_neg])
    | (unfold GroundTheory.PAdicHodge.Laurent.cmul
       funext n
       simp [tsum_neg, mul_neg])

