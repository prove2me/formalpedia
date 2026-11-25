-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.wordOp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:52:52.544826+00:00
-- url     : https://prove2.me/submissions/4d309391-0d46-487a-b0f7-4480c28d9ef1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_succ
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_wordOp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_Ad_inv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_map


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
open scoped ContDiff
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) (g : G) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      h.wordOp π Y (π g v) = π g (h.wordOp π (fun i => h.Ad g⁻¹ (Y i)) v)
  | 0, _ => rfl
  | k + 1, Y => by
    rw [wordOp_succ, solution hv g (Fin.tail Y), wordOp_succ]
    have := h.derivOp_map π (h.isSmoothVector_wordOp π hv (fun i => h.Ad g⁻¹ (Fin.tail Y i)))
      g (h.Ad g⁻¹ (Y 0))
    rw [Ad_Ad_inv] at this
    rw [this]
    rfl
end GroundTheory.Automorphic.IsExpLieAlgebra
