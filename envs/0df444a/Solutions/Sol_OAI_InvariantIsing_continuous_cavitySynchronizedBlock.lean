-- Prove2me | solution 1 for OAI.InvariantIsing.continuous_cavitySynchronizedBlock
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:20.720328+00:00
-- url     : https://prove2.me/submissions/417f1c5a-408d-4712-abc9-5752e017bd17

import Mathlib
import Definitions.Def_OAIQ258001

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCascadeSpectralLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Synchronized spectral labels are retained in the finite-cascade
approximation of the scalar GG overlap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavitySynchronizedBlock_oai {m r : ℕ} (d : SpectralEntry m)
    (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a)) :
    Continuous (cavitySynchronizedBlock (r := r) d f) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  by_cases hij : i = j
  · simp only [cavitySynchronizedBlock, ite_eq_left hij]
    exact continuous_const
  · simp only [cavitySynchronizedBlock, ite_eq_right hij]
    exact (hf a).comp (by fun_prop)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.continuous_cavitySynchronizedBlock_oai := @OAI.InvariantIsing.continuous_cavitySynchronizedBlock_oai
