-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.psum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:28.538026+00:00
-- url     : https://prove2.me/submissions/f3baf33f-0807-4853-90f9-218016d07f9c

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
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (a b : ℕ) :
    psum A g w (a + b) = psum A g w a + A (g ^ a) (psum A g w b) := by
  induction a with
  | zero => simp [psum_zero, hone]
  | succ a ih =>
    rw [Nat.add_right_comm, psum_succ, psum_succ, ih, map_add, pow_succ', hmul _ hg _ (pow_mem hg a),
      add_assoc]
end GlobalTheory.Cyc.Procyclic
