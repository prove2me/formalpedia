-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.norm_move_psum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:43.304379+00:00
-- url     : https://prove2.me/submissions/b18d9e94-e7f3-49ec-9e27-6e95e0115d14

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
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_succ

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
theorem _root_.solution (hg : g ∈ G)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (hn : ∀ y, ‖A g y‖ ≤ ‖y‖)
    (q n : ℕ) : ‖A (g ^ q) (psum A g w n) - psum A g w n‖ ≤ ‖A (g ^ q) w - w‖ := by
  induction n with
  | zero => simp [psum_zero]
  | succ n ih =>
    have h : A (g ^ q) (psum A g w (n + 1)) - psum A g w (n + 1)
        = (A (g ^ q) w - w) + A g (A (g ^ q) (psum A g w n) - psum A g w n) := by
      rw [psum_succ, map_add, map_sub, ← hmul _ (pow_mem hg q) _ hg, ← hmul _ hg _ (pow_mem hg q),
        ← pow_succ, ← pow_succ']
      abel
    rw [h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ((hn _).trans ih))
end GlobalTheory.Cyc.Procyclic
