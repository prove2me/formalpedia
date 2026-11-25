-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.isSmooth_mGenQuotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:24.141523+00:00
-- url     : https://prove2.me/submissions/a9fa0917-939f-4f3d-a4b0-3660e7a42194

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain
import Theorems.Thm_GroundTheory_Automorphic_GKTensor_isSmooth_mGenSubrep
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotRep_mk


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
theorem _root_.solution (hτ : IsSmooth τ) (e : End ℂ V) (N : Submodule ℂ V) :
    IsSmooth (mGenQuotRep τ e N) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (mGenSubrep τ N).toRepresentation u)
    (fun g hg => ?_) (isSmooth_mGenSubrep hτ N u)
  show mGenQuotRep τ e N g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [mGenQuotRep_mk, hg]
end GroundTheory.Automorphic.GKTensor
