-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_wordOp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:50.641343+00:00
-- url     : https://prove2.me/submissions/7d9b1792-28b2-46c4-b655-9adeff476801

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_map
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_wordOp_cml
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_Ad_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_apply_apply

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
    {k : ℕ} (Y : Fin k → 𝔤) : Continuous fun g : G => h.wordOp π Y (π g v) := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  have e : (fun g : G => h.wordOp π Y (π g v)) =
      fun g => π g (Φ (fun i => h.Ad g⁻¹ (Y i))) := by
    funext g; rw [h.wordOp_map π hv, hΦ]
  rw [e]
  refine continuous_apply_apply π hπ continuous_id (Φ.cont.comp ?_)
  exact continuous_pi fun i => (h.continuous_Ad_apply (Y i)).comp continuous_inv
end GroundTheory.Automorphic.IsExpLieAlgebra
