-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.comp_transposeGL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:40:24.177126+00:00
-- url     : https://prove2.me/submissions/2cc70942-d1d6-43da-85ee-3681db50a06b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan

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
theorem _root_.solution {U : Set (GL (Fin n) F)}
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    (fun x => f (transposeGL x)) ∈ supportedIn U :=
  ⟨⟨hf.1.1.comp_continuous continuous_transposeGL, hf.1.2.comp_homeomorph transposeHomeo⟩,
    fun x hx => (hUτ x).1 (hf.2 hx)⟩
end GroundTheory.Automorphic.ContragredientTranspose
