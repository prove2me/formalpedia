-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:45.668801+00:00
-- url     : https://prove2.me/submissions/0739bbad-a6c7-4ca8-99b3-42105bce78d3

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp006

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

lemma compatibleFrame_inverse_left_bp240_oai {J : End n} (hJ : Compatible J) (v : Phase n) :
    (compatibleFrame J).inverse (compatibleFrame J v) = v := by
  obtain ⟨e,he⟩ := compatibleFrame_invertible hJ
  rw [←he]
  simp only [ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_inverse_left_bp240_oai
