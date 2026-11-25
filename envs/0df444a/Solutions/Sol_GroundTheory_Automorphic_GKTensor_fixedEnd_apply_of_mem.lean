-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.fixedEnd_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:56.112865+00:00
-- url     : https://prove2.me/submissions/27846381-2788-43ec-a2be-e2b6bf5a5791

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


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
theorem _root_.solution {v : V} (hv : v ∈ fixedVectors τ H) :
    fixedEnd hτ hHc hHo v = v :=
  fixedProj_apply_of_mem hτ hHc hHo hv
end GroundTheory.Automorphic.GKTensor
