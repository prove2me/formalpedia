-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.norm_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:25.726205+00:00
-- url     : https://prove2.me/submissions/3548ccf2-f272-4c2b-b4d0-fdb829fe2a0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest
namespace GlobalTheory.DiscreteSeriesTest
theorem _root_.solution {ε : Fin 1 → Bool} {g : Matrix (Fin 1) (Fin 1) ℂ} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by
  have h := congrFun (congrFun hg 0) 0
  simp only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  have h2 := congrArg norm h
  have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  simp only [norm_mul, norm_star, h3] at h2
  nlinarith [norm_nonneg (g 0 0)]
end GlobalTheory.DiscreteSeriesTest
