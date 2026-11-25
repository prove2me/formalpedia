-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_brSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:11.696313+00:00
-- url     : https://prove2.me/submissions/5adfaecf-6af2-4c89-8ff1-e70ea114325d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_wordOp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_zero

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
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.brSum π X Y v)
  | 0, _ => h.isSmoothVector_zero π
  | _ + 1, Y => (h.smoothVectors π).add_mem
      (h.isSmoothVector_derivOp π (h.isSmoothVector_wordOp π hv _) _)
      (h.isSmoothVector_derivOp π (solution hv X (Fin.tail Y)) _)
end GroundTheory.Automorphic.IsExpLieAlgebra
