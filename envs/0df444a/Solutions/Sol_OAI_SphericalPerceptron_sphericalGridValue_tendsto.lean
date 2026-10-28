-- Prove2me | solution 1 for OAI.SphericalPerceptron.sphericalGridValue_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:50:19.676923+00:00
-- url     : https://prove2.me/submissions/23e31469-1d61-49c6-a677-debe027c7f36

import Mathlib
import Definitions.Def_OAIB3Sp000
import Theorems.Thm_OAI_SphericalPerceptron_sphericalGridValue_compact_uniform

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

lemma sphericalGridValue_tendsto_oai (k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Tendsto (fun n => sphericalGridValue n k v) atTop (𝓝 (sphericalGridDual k v)) := by
  have hu := sphericalGridValue_compact_uniform k (∑ i, v i)
  apply hu.tendsto_at
  exact ⟨hv,fun i => Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)⟩

end SphericalPerceptron
end
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptron.sphericalGridValue_tendsto_oai := @OAI.SphericalPerceptron.sphericalGridValue_tendsto_oai
