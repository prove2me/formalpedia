-- Prove2me | solution 1 for OAI.PosteriorReplicas.source_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:34:57.551476+00:00
-- url     : https://prove2.me/submissions/d006135c-140b-4c74-8dce-a442454a510a

import Mathlib
import Definitions.Def_PosteriorReplicas
import Theorems.Thm_OAI_PosteriorRegression_kernel_subquadratic_memory
import Theorems.Thm_OAI_PosteriorReplicas_distanceReplicaBlock
import Theorems.Thm_OAI_PosteriorReplicas_equalLabelMeasureIdentity
import Theorems.Thm_OAI_PosteriorReplicas_equalLabelVersions
import Theorems.Thm_OAI_PosteriorReplicas_gaussianReplicaBlock
import Theorems.Thm_OAI_PosteriorReplicas_haarReplicaBlock
import Theorems.Thm_OAI_PosteriorReplicas_incidenceReplicaBlock
import Theorems.Thm_OAI_PosteriorReplicas_syntheticReplicaBlock

section
-- module Solutions.OAIQW_PosteriorReplicas.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PosteriorReplicas
universe u

theorem source_main_oai : EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.KernelSubquadraticMemory.{u} :=
  ⟨equalLabelMeasureIdentity, equalLabelVersions, gaussianReplicaBlock,
    distanceReplicaBlock, haarReplicaBlock, syntheticReplicaBlock,
    incidenceReplicaBlock, PosteriorRegression.kernel_subquadratic_memory⟩
end PosteriorReplicas

end OAI
end

theorem solution.{u} : type_of% @OAI.PosteriorReplicas.source_main_oai.{u} := @OAI.PosteriorReplicas.source_main_oai.{u}
