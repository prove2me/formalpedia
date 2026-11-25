-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_wordOp_cml
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:07.902425+00:00
-- url     : https://prove2.me/submissions/cbd94612-d012-4473-90a5-39a595b00b9b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_continuous_multilinear_of_finiteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_wordML

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
theorem _root_.solution {v : E} (hv : h.IsSmoothVector π v) (k : ℕ) :
    ∃ Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E, ∀ Y, Φ Y = h.wordOp π Y v := by
  let M : MultilinearMap ℝ (fun _ : Fin k => 𝔤) E :=
    ((h.smoothVectors π).subtype.restrictScalars ℝ).compMultilinearMap (h.wordML π hv k)
  refine ⟨⟨M, continuous_multilinear_of_finiteDimensional M⟩, fun Y => ?_⟩
  show ((h.wordML π hv k Y : h.smoothVectors π) : E) = _
  exact h.coe_wordML π hv k Y
end GroundTheory.Automorphic.IsExpLieAlgebra
