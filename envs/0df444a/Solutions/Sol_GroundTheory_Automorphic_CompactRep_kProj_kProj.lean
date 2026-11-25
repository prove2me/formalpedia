-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.kProj_kProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:26:25.558683+00:00
-- url     : https://prove2.me/submissions/f5b7374c-5d72-44a6-8571-501c3d622140

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_apply_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_mem_component

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
theorem _root_.solution (v : X) : kProj hσ hc (kProj hσ hc v) = kProj hσ hc v :=
  (kProj_apply_eq_self_iff hσ hc).2 (kProj_mem_component hσ hc v)
end GroundTheory.Automorphic.CompactRep
