-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.isWinProj_kProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:29.347076+00:00
-- url     : https://prove2.me/submissions/d207cdad-cfcb-4034-a2fa-8517462667e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_kProj
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_mem

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
theorem _root_.solution {M : Type*} [Monoid M] {ρ : Representation ℂ M X}
    (hsub : ∀ Y : Subrepresentation ρ, ∀ k, ∀ y ∈ Y.toSubmodule, σ k y ∈ Y.toSubmodule) :
    IsWinProj ρ (kProj hσ hc) :=
  ⟨kProj_kProj hσ hc, fun Y _ hy => kProj_mem hσ hc (hsub Y) hy⟩
end GroundTheory.Automorphic.CompactRep
