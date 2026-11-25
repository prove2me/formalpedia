-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_Ad_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:56.20799+00:00
-- url     : https://prove2.me/submissions/80ebfc99-bd21-4083-8d6b-4cc2e9101f6f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X : 𝔤) : Continuous fun g : G => h.Ad g X := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun g : G => ((g : 𝔸ˣ) : 𝔸) := continuous_val_val G
  have h2 : Continuous fun g : G => (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) := h1.comp continuous_inv
  exact (h1.mul continuous_const).mul h2
end GroundTheory.Automorphic.IsExpLieAlgebra
