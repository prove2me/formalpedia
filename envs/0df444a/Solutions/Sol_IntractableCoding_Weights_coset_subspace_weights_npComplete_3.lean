-- Prove2me | solution 3 for IntractableCoding.Weights.coset_subspace_weights_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:55.124969+00:00
-- url     : https://prove2.me/submissions/3ea91408-71fd-4b4e-845f-60c385046f75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_IntractableCoding_Weights_Problems
import Definitions.Def_IntractableCoding_Weights_Reductions
import Theorems.Thm_IntractableCoding_Weights_cosetWeights_mem_NP
import Theorems.Thm_IntractableCoding_Weights_subspaceWeights_mem_NP
import Theorems.Thm_IntractableCoding_Weights_npHard_of_threeDM_reduction
import Theorems.Thm_IntractableCoding_Weights_cosetOf3DM_polyTime
import Theorems.Thm_IntractableCoding_Weights_coset_reduction_iff
import Theorems.Thm_IntractableCoding_Weights_subspaceOf3DM_polyTime
import Theorems.Thm_IntractableCoding_Weights_subspace_reduction_iff

open IntractableCoding.Weights

theorem solution :
    NPCompleteFor encodeCoset CosetWeightsYes ∧
      NPCompleteFor encodeSubspace SubspaceWeightsYes :=
  ⟨⟨cosetWeights_mem_NP,
    npHard_of_threeDM_reduction encodeCoset CosetWeightsYes cosetOf3DM
      cosetOf3DM_polyTime coset_reduction_iff⟩,
   ⟨subspaceWeights_mem_NP,
    npHard_of_threeDM_reduction encodeSubspace SubspaceWeightsYes subspaceOf3DM
      subspaceOf3DM_polyTime subspace_reduction_iff⟩⟩
