-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.exists_norm_psum_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:58.009506+00:00
-- url     : https://prove2.me/submissions/84473928-b454-42e9-8ceb-d14408f6074a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_psum_add
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_norm_psum_le
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_norm_psum_mul_sub_le

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
theorem _root_.solution (p : ℕ) (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ a d : ℕ, p ^ k ∣ d → ‖psum A g w (a + d) - psum A g w a‖ ≤ ε := by
  obtain ⟨k, hk⟩ := hD ε hε
  obtain ⟨s, hs⟩ := hp ε hε
  refine ⟨k + s, ?_⟩
  rintro a _ ⟨t, rfl⟩
  rw [psum_add hg hone hmul, add_sub_cancel_left]
  refine (hn _ (pow_mem hg a) _).trans ?_
  have h : psum A g w (p ^ (k + s) * t)
      = (psum A g w (p ^ k * (p ^ s * t)) - (p ^ s * t) • psum A g w (p ^ k))
        + p ^ s • (t • psum A g w (p ^ k)) := by
    rw [pow_add, mul_assoc, smul_smul]; abel
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_psum_mul_sub_le hg hone hmul (hn g hg) _ _).trans hk) (hs _ ?_))
  exact (IsUltrametricDist.norm_nsmul_le _ _).trans (norm_psum_le (hn g hg) _)
end GlobalTheory.Cyc.Procyclic
