-- Prove2me | solution 1 for OAI.JointDickmanPaper.joint_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:00:21.63269+00:00
-- url     : https://prove2.me/submissions/3b6fd8af-445e-47c6-9bc2-1d604d8e7e03

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_JointDickman
import Definitions.Def_OAIQ083J001
import Theorems.Thm_OAI_JointDickman_jointDickmanLaw_unconditional_jd

section
-- module Solutions.OAIQ083_JD.JointDickman_PaperMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint Dickman law for consecutive integers -/

namespace JointDickmanPaper

open Filter JointDickman
open scoped Topology

/-- Theorem 1: ordinary natural density, with both thresholds based at `n`. -/
theorem joint_law_oai (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (fun n =>
      (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b))
      atTop (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b))) :=
  jointDickmanLaw_unconditional_jd a b ha ha1 hb hb1

end JointDickmanPaper

end OAI
end

theorem solution : type_of% @OAI.JointDickmanPaper.joint_law_oai := @OAI.JointDickmanPaper.joint_law_oai
