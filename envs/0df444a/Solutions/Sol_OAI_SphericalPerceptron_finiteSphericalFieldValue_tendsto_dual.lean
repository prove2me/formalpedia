-- Prove2me | solution 1 for OAI.SphericalPerceptron.finiteSphericalFieldValue_tendsto_dual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:56.035042+00:00
-- url     : https://prove2.me/submissions/d7edb1c3-707f-41a9-9b49-5bc73aef6ebe

import Mathlib
import Definitions.Def_SphericalField
import Theorems.Thm_OAI_SphericalPerceptron_finiteSphericalFieldValue_pointwise_dual

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_DepthUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma finiteSphericalFieldValue_tendsto_dual_oai {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
      (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1))) := by
  obtain ⟨q,hq,hq1,hleast,hlim⟩ := finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh hh0
  exact hlim

end SphericalPerceptron
end
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptron.finiteSphericalFieldValue_tendsto_dual_oai := @OAI.SphericalPerceptron.finiteSphericalFieldValue_tendsto_dual_oai
