-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.trace_Jm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:42.235014+00:00
-- url     : https://prove2.me/submissions/28e24fb4-5a56-4a70-9098-17f4522bc39e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    (Jm ε).trace = 2 * ((univ.filter fun i => ε i = true).card : ℂ) - n := by
  unfold Jm
  rw [Matrix.trace_diagonal]
  have : ∀ a, (if ε a = true then (1 : ℂ) else -1) = 2 * (if ε a = true then 1 else 0) - 1 := by
    intro a; split_ifs <;> norm_num
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
end GlobalTheory.UnitaryCayley
