-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.finite_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:06.386304+00:00
-- url     : https://prove2.me/submissions/bec8823a-2bfa-41e0-b9e8-6ba72c85bbda

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_cocycle_mul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_index_cocycleKer
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_finite_right_invariant
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_isOpen_cocycleKer
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cocycles
namespace GlobalTheory.CompanionTheory.Cocycles
theorem _root_.solution : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V →
    (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) →
    {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  intro k G _ _ _ _ A _ hV hN
  refine ((hN (Nat.card (A.V × (A.V → A.V)))).biUnion (fun H hH => finite_right_invariant H hH.2.1)).subset ?_
  rintro f ⟨hlc, hf⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨cocycleKer A.ρ f hf, ⟨isOpen_cocycleKer A hlc hf, index_cocycleKer hf⟩,
    fun g c hc => cocycle_mul_mem hf g hc⟩
end GlobalTheory.CompanionTheory.Cocycles
