-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.wordOp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:18.302089+00:00
-- url     : https://prove2.me/submissions/0d7dd6b0-f37c-4946-895f-00f323fa564b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_add
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_neg

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
theorem _root_.solution {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w)
    {k : ℕ} (Y : Fin k → 𝔤) : h.wordOp π Y (v - w) = h.wordOp π Y v - h.wordOp π Y w := by
  have hw' : h.IsSmoothVector π (-w) := (h.smoothVectors π).neg_mem hw
  rw [sub_eq_add_neg, h.wordOp_add π hv hw', h.wordOp_neg π hw, ← sub_eq_add_neg]
end GroundTheory.Automorphic.IsExpLieAlgebra
