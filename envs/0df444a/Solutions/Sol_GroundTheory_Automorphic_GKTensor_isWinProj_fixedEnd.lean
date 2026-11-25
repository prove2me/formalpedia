-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.isWinProj_fixedEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:45.824376+00:00
-- url     : https://prove2.me/submissions/5e68a076-9bbd-4dc0-93bf-0f114a31b205

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Theorems.Thm_GroundTheory_Automorphic_GKTensor_fixedEnd_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_GKTensor_fixedEnd_mem
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_fixedProj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module RestrictedTensor CompactRep
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.GKTensor
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ L V} (hτ : IsSmooth τ)
  {H : Subgroup L} (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))
namespace GroundTheory.Automorphic.GKTensor
theorem _root_.solution : IsWinProj τ (fixedEnd hτ hHc hHo) :=
  ⟨fun v => fixedEnd_apply_of_mem hτ hHc hHo (fixedEnd_mem hτ hHc hHo v),
    fun Y _ hy => fixedProj_mem hτ hHc hHo Y hy⟩
end GroundTheory.Automorphic.GKTensor
