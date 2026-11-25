-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.norm_psum_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:43.936275+00:00
-- url     : https://prove2.me/submissions/157486ed-5fbd-447d-8cb4-6452f5f1239a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_zero
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_add
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_norm_move_psum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]
variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}
variable [IsUltrametricDist X]
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (hn : ∀ y, ‖A g y‖ ≤ ‖y‖)
    (q t : ℕ) : ‖psum A g w (q * t) - t • psum A g w q‖ ≤ ‖A (g ^ q) w - w‖ := by
  induction t with
  | zero => simp [psum_zero]
  | succ t ih =>
    have h : psum A g w (q * (t + 1)) - (t + 1) • psum A g w q
        = (A (g ^ q) (psum A g w (q * t)) - psum A g w (q * t))
          + (psum A g w (q * t) - t • psum A g w q) := by
      rw [mul_add, mul_one, add_comm (q * t) q, psum_add hg hone hmul, succ_nsmul]
      abel
    rw [h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_move_psum_le hg hmul hn _ _) ih)
end GlobalTheory.Cyc.Procyclic
