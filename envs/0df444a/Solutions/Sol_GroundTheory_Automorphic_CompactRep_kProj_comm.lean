-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.kProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:37.07991+00:00
-- url     : https://prove2.me/submissions/36100b66-9b72-4a20-916b-a2c5271f3b8b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_comm


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
theorem _root_.solution {T : End ℂ X} (hT : ∀ k, T * σ k = σ k * T) (v : X) :
    kProj hσ hc (T v) = T (kProj hσ hc v) := by
  haveI := isSemisimpleModule_asModule hσ
  let f : Representation.IntertwiningMap σ σ := ⟨T, hT⟩
  exact isoProj_comm hc (Representation.IntertwiningMap.equivLinearMapAsModule σ σ f) v
end GroundTheory.Automorphic.CompactRep
