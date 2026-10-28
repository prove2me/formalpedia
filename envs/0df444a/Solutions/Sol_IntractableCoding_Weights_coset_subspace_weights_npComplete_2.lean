-- Prove2me | solution 2 for IntractableCoding.Weights.coset_subspace_weights_npComplete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:20:07.484892+00:00
-- url     : https://prove2.me/submissions/cb4def60-d0e3-4d5b-8eb9-fb29e31806e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_IntractableCoding_Weights_Problems
import Definitions.Def_IntractableCoding_Weights_Reductions
import Theorems.Thm_IntractableCoding_Weights_npHard_of_threeDM_reduction
import Theorems.Thm_IntractableCoding_Weights_cosetWeights_mem_NP
import Theorems.Thm_IntractableCoding_Weights_subspaceWeights_mem_NP
import Theorems.Thm_IntractableCoding_Weights_cosetOf3DM_polyTime
import Theorems.Thm_IntractableCoding_Weights_subspaceOf3DM_polyTime
import Theorems.Thm_IntractableCoding_Weights_coset_reduction_iff
import Theorems.Thm_IntractableCoding_Weights_subspace_reduction_iff

open IntractableCoding.Weights

/-- COSET WEIGHTS and SUBSPACE WEIGHTS are both NP-complete: each is in NP and NP-hard under
polynomial-time TM2 many-one reductions, for the binary encodings `encodeCoset` and
`encodeSubspace`. -/
theorem solution :
    NPCompleteFor encodeCoset CosetWeightsYes ∧
      NPCompleteFor encodeSubspace SubspaceWeightsYes :=
  ⟨⟨cosetWeights_mem_NP,
    npHard_of_threeDM_reduction encodeCoset CosetWeightsYes cosetOf3DM
      cosetOf3DM_polyTime coset_reduction_iff⟩,
   ⟨subspaceWeights_mem_NP,
    npHard_of_threeDM_reduction encodeSubspace SubspaceWeightsYes subspaceOf3DM
      subspaceOf3DM_polyTime subspace_reduction_iff⟩⟩
