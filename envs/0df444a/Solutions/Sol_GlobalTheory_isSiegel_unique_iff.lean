-- Prove2me | solution 1 for GlobalTheory.isSiegel_unique_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:16.30848+00:00
-- url     : https://prove2.me/submissions/59e7dd72-4ede-4a6e-9aea-5d25c4f26714

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_isSiegel_diagonal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
namespace GlobalTheory
theorem _root_.solution [Unique ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ 0 < (Ω default default).im := by
  classical
  have : Ω = diagonal fun _ => Ω default default := by
    ext i j
    obtain rfl := Subsingleton.elim i default
    obtain rfl := Subsingleton.elim j default
    simp
  rw [this, isSiegel_diagonal_iff]
  simp
end GlobalTheory
