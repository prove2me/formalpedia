-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_wordOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:19.473575+00:00
-- url     : https://prove2.me/submissions/7eaf00ef-1a05-4b27-bcc5-c89de8da1411

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
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.wordOp π Y v)
  | 0, _ => hv
  | _ + 1, Y => h.isSmoothVector_derivOp π (solution hv (Fin.tail Y)) (Y 0)
end GroundTheory.Automorphic.IsExpLieAlgebra
