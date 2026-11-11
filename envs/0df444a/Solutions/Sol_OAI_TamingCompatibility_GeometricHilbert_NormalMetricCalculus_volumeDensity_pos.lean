-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:11:38.057648+00:00
-- url     : https://prove2.me/submissions/79b5d44f-89a4-428f-985a-190d0812d7b1

import Mathlib
import Definitions.Def_OAIQ239Tc017

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupMetricTensorV_1_ref1d17_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_1_ref1d17_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
lemma volumeDensity_pos_oai {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
    0 < volumeDensity M := Real.sqrt_pos.mpr hM.1

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos_oai := @OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos_oai
