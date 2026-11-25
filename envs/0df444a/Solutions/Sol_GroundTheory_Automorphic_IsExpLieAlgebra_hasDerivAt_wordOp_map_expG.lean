-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_wordOp_map_expG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:19.447242+00:00
-- url     : https://prove2.me/submissions/ce767dc7-8d21-4658-9e2a-448a3896833d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_map
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_wordOp_expG

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
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    (X : 𝔤) (g : G) {k : ℕ} (Y : Fin k → 𝔤) :
    HasDerivAt (fun t : ℝ => h.wordOp π Y (π g (π (h.expG (t • X)) v)))
      (h.wordOp π Y (π g (h.derivOp π X v))) 0 := by
  have e : (fun t : ℝ => h.wordOp π Y (π g (π (h.expG (t • X)) v))) =
      fun t => ((π g).restrictScalars ℝ)
        (h.wordOp π (fun i => h.Ad g⁻¹ (Y i)) (π (h.expG (t • X)) v)) := by
    funext t
    rw [h.wordOp_map π (h.isSmoothVector_map π hv _)]
    rfl
  rw [e, h.wordOp_map π (h.isSmoothVector_derivOp π hv X)]
  exact ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (h.hasDerivAt_wordOp_expG π hπ hv X _)
end GroundTheory.Automorphic.IsExpLieAlgebra
