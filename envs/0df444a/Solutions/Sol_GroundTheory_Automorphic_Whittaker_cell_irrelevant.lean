-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cell_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:53.883457+00:00
-- url     : https://prove2.me/submissions/56c59fe3-87d6-40fe-b1ea-ec6dd7ffd21d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isClosed_cellLe
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_fiber_eq_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_irrelevant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mul_mem_cellSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_cellMinor
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_forall_fiber


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hψ : Continuous ψ₀) {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hirr : ∀ t, Irrelevant ψ₀ (bruhatCell g) t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  intro f hf
  refine mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor (bruhatCell g))
    le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hf fun y => ?_
  by_cases hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor (bruhatCell g) x = y
  · obtain ⟨x, hxU, hxC, rfl⟩ := hy
    obtain ⟨t, ht⟩ := fiber_eq_orbit hUge hcellU hxU hxC
    have hC : IsClosed (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x}) :=
      (isClosed_cellLe g).inter (isClosed_singleton.preimage (continuous_cellMinor _))
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv ht (hirr t) hf)
    rw [← hab]
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ha)) (Submodule.mem_sup_right hb)
  · refine le_sup_right (a := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)))
      ⟨hf, fun x hx => ?_⟩
    by_contra hfx
    exact hy ⟨x, hf.2 hfx, hx.1, hx.2⟩
end GroundTheory.Automorphic.Whittaker
