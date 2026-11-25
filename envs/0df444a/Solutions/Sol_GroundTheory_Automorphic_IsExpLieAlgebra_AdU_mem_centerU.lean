-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.AdU_mem_centerU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:02.304995+00:00
-- url     : https://prove2.me/submissions/ca3ed2cb-3c9c-462b-aca9-f70d5551b9b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_apply_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (g : G) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) : h.AdU g z ∈ h.centerU := by
  rw [centerU, Subalgebra.mem_center_iff] at hz ⊢
  intro u
  rw [← h.AdU_apply_inv g u, ← map_mul, ← map_mul, hz]
end GroundTheory.Automorphic.IsExpLieAlgebra
