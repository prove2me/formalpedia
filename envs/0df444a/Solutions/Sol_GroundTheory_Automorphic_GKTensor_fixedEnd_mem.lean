-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.fixedEnd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:08.446861+00:00
-- url     : https://prove2.me/submissions/c62099d6-9955-4646-b652-7944969109ca

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor

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
theorem _root_.solution (v : V) : fixedEnd hτ hHc hHo v ∈ fixedVectors τ H :=
  (fixedProj τ hτ hHc hHo v).2
end GroundTheory.Automorphic.GKTensor
