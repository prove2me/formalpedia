-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.wordOp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:52.756042+00:00
-- url     : https://prove2.me/submissions/569f6352-662a-481c-be91-1fc95b9284c9

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
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) (c : ℂ) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.wordOp π Y (c • v) = c • h.wordOp π Y v
  | 0, _ => rfl
  | _ + 1, Y => by
    rw [wordOp_succ, solution hv c (Fin.tail Y),
      h.derivOp_smul π (h.isSmoothVector_wordOp π hv _)]
    rfl
end GroundTheory.Automorphic.IsExpLieAlgebra
