-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.GoodPiece.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:43.112809+00:00
-- url     : https://prove2.me/submissions/c68effc8-55a4-4548-9ce4-6e4c46dd5cb7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_one
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_of_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
namespace GroundTheory.Automorphic.Whittaker
namespace GoodPiece
theorem _root_.solution (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) {A : Set X}
    (hA : GoodPiece (H := H) U C x₀ W A) (h : H) : GoodPiece (H := H) U C x₀ W (h • A) := by
  intro g hg hgA
  have h1 : transl h⁻¹ g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
    refine hA _ (transl_mem_supportedIn hUinv _ hg) fun x hx => ?_
    rw [transl_apply, inv_inv, hgA _ (mem_orbit_of_mem_orbit h hx)]
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem (Set.smul_mem_smul_set hxA)]
      rfl
    · rw [Set.indicator_of_notMem hxA,
        Set.indicator_of_notMem (fun h' => hxA ((Set.smul_mem_smul_set_iff).1 h'))]
  have := transl_mem_of_mem χ hWU hW h h1
  rwa [← transl_mul, mul_inv_cancel, transl_one] at this
end GoodPiece
end GroundTheory.Automorphic.Whittaker
