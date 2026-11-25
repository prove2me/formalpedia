-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.wordOp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:56.930466+00:00
-- url     : https://prove2.me/submissions/5797fb0d-b7f0-4b62-88cd-5f559a4f09c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_succ
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_wordOp

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
theorem _root_.solution {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.wordOp π Y (v + w) = h.wordOp π Y v + h.wordOp π Y w
  | 0, _ => rfl
  | _ + 1, Y => by
    rw [wordOp_succ, solution hv hw (Fin.tail Y),
      h.derivOp_add π (h.isSmoothVector_wordOp π hv _) (h.isSmoothVector_wordOp π hw _)]
    rfl
end GroundTheory.Automorphic.IsExpLieAlgebra
