-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.kProj_mem_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:19:28.096123+00:00
-- url     : https://prove2.me/submissions/1dfc3691-f2fa-451f-9487-fb44df039707

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_mem_isotypicComponent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set RestrictedTensor
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}
variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)
namespace GroundTheory.Automorphic.CompactRep
theorem _root_.solution (v : X) : (kProj hσ hc v : σ.asModule) ∈ c := by
  haveI := isSemisimpleModule_asModule hσ
  exact isoProj_mem_isotypicComponent hc _
end GroundTheory.Automorphic.CompactRep
