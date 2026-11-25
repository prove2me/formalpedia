-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.kProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:55.785514+00:00
-- url     : https://prove2.me/submissions/2aca0b9f-7765-4eed-8d8a-633f801ce64c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_mem


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
theorem _root_.solution {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) {y : X} (hy : y ∈ Y) :
    kProj hσ hc y ∈ Y := by
  haveI := isSemisimpleModule_asModule hσ
  let P : Subrepresentation σ := ⟨Y, fun k y hy => hY k y hy⟩
  exact isoProj_mem hc (Subrepresentation.subrepresentationSubmoduleOrderIso P) hy
end GroundTheory.Automorphic.CompactRep
