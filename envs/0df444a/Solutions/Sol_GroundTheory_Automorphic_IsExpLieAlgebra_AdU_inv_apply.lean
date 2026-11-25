-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.AdU_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:24.184866+00:00
-- url     : https://prove2.me/submissions/bdbf9a1a-da20-40e8-874e-9e84fcb0f87a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_mul
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_one

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
theorem _root_.solution (g : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.AdU g⁻¹ (h.AdU g u) = u := by
  rw [← AlgHom.comp_apply, ← AdU_mul, inv_mul_cancel, AdU_one, AlgHom.id_apply]
end GroundTheory.Automorphic.IsExpLieAlgebra
