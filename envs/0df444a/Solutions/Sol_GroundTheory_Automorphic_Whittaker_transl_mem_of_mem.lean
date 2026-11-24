-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:11.723858+00:00
-- url     : https://prove2.me/submissions/613bea80-f23b-430c-8b5e-0dd2a0e55e2c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan

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
  [TopologicalSpace H] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) (h : H)
    {f : X → ℂ} (hf : f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    transl h f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  have hfU : f ∈ supportedIn U := (sup_le hWU inf_le_left) hf
  have e : transl h f = (transl h f - χ h • f) + χ h • f := by abel
  rw [e]
  exact add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
    (hW (sub_mem_relSpan χ h hfU))) (Submodule.smul_mem _ _ hf)
end GroundTheory.Automorphic.Whittaker
