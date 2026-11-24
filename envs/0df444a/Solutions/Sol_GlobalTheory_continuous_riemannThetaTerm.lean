-- Prove2me | solution 1 for GlobalTheory.continuous_riemannThetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:48.17737+00:00
-- url     : https://prove2.me/submissions/dc0afa03-73e1-4870-a727-a4bb5efde4f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

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
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
theorem _root_.solution (a b : ι → ℝ) (n : ι → ℤ) :
    Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannThetaTerm a b p.2 p.1 n := by
  have (i j : ι) : Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => p.2 i j :=
    continuous_snd.matrix_elem i j
  simp only [riemannThetaTerm_eq_sum]
  fun_prop
end GlobalTheory
