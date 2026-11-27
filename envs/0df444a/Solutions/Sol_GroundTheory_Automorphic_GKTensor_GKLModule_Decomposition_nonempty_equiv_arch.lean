-- Prove2me | solution 1 for GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition.nonempty_equiv_arch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:08.273165+00:00
-- url     : https://prove2.me/submissions/a44245a1-23d2-4d44-8b84-7ef52294eac5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_fst_of_equiv
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans


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
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
open GroundTheory.Automorphic.GKTensor.GKLModule
variable (Mx : GKLModule h K L V)
attribute [instance] Decomposition.instAddCommGroup₁ Decomposition.instModule₁
  Decomposition.instAddCommGroup₂ Decomposition.instModule₂
open GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition
variable {Mx}
namespace GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition
theorem _root_.solution (D D' : Mx.Decomposition) : Nonempty (D.π₁.rep.Equiv D'.π₁.rep) :=
  nonempty_equiv_fst_of_equiv D.isIrreducible₁ D.isIrreducible₂ D'.isIrreducible₁
    (D.equiv.symm.trans D'.equiv)
end GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition
