-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.relT_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:43.824606+00:00
-- url     : https://prove2.me/submissions/a4473aeb-8a39-485d-bc34-00ff7dcb2490

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_mono


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
theorem _root_.solution {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) : relT U ≤ relT V := by
  refine sup_le_sup (Submodule.span_mono ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨h, f, hf, rfl⟩
    exact ⟨h, f, supportedIn_mono hUV hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, supportedIn_mono hUV hf, rfl⟩
end GroundTheory.Automorphic.ContragredientTranspose
