-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.tauSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:43.006982+00:00
-- url     : https://prove2.me/submissions/22639947-cac4-4d51-bd82-a33b593246a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_comp_transposeGL_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
omit [IsTopologicalRing F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {U : Set (GL (Fin n) F)} (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) :
    tauSpan U ≤ supportedIn U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  exact (supportedIn U).add_mem hf (comp_transposeGL_mem hUτ hf)
end GroundTheory.Automorphic.ContragredientTranspose
