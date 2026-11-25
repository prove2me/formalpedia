-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_norm_wordOp_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:36.066808+00:00
-- url     : https://prove2.me/submissions/62981329-2621-4c64-9997-272201091b76

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_map
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_wordOp_cml

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
    {k : ℕ} (Y : Fin k → 𝔤) : ∃ C, ∀ g : G, ‖h.wordOp π Y (π g v)‖ ≤ C * ‖h.AdL g⁻¹‖ ^ k := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  refine ⟨‖Φ‖ * ∏ i, ‖Y i‖, fun g => ?_⟩
  rw [h.wordOp_map π hv, ← hΦ]
  calc ‖π g (Φ (fun i => h.Ad g⁻¹ (Y i)))‖ ≤ ‖π g‖ * ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ := by gcongr; exact hπ _
    _ = ‖Φ (fun i => h.Ad g⁻¹ (Y i))‖ := one_mul _
    _ ≤ ‖Φ‖ * ∏ i, ‖h.Ad g⁻¹ (Y i)‖ := Φ.le_opNorm _
    _ ≤ ‖Φ‖ * ∏ i, (‖h.AdL g⁻¹‖ * ‖Y i‖) := by
        gcongr with i
        exact (h.AdL g⁻¹).le_opNorm (Y i)
    _ = (‖Φ‖ * ∏ i, ‖Y i‖) * ‖h.AdL g⁻¹‖ ^ k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
end GroundTheory.Automorphic.IsExpLieAlgebra
