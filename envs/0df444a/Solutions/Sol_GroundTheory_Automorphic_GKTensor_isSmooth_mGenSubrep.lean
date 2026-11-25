-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.isSmooth_mGenSubrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:42:44.060122+00:00
-- url     : https://prove2.me/submissions/25066692-3706-48ce-a2ff-bd17286a6e1e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain

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
open Set Module RestrictedTensor CompactRep TensorProduct
open scoped TensorProduct
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}
  [CompactSpace K]
open GroundTheory.Automorphic.GKTensor
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {τ : Representation ℂ L V}
namespace GroundTheory.Automorphic.GKTensor
theorem _root_.solution (hτ : IsSmooth τ) (N : Submodule ℂ V) :
    IsSmooth (mGenSubrep τ N).toRepresentation := by
  intro u
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf τ (u : V)) (fun g hg => ?_) (hτ u)
  exact Subtype.ext hg
end GroundTheory.Automorphic.GKTensor
