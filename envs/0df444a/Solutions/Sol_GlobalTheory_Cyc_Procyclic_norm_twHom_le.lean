-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.norm_twHom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:53.869082+00:00
-- url     : https://prove2.me/submissions/7908ecb3-ff0f-4a69-8c5d-0e4e57bcbbb8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_chiC_mem_intC
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_apply

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
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) :
    ∀ σ ∈ Gj K m, ∀ y, ‖twHom act χ i U σ y‖ ≤ ‖y‖ := by
  intro σ hσ y
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  rw [twHom_apply, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (chiC_mem_intC hχ (Ks K m) i σ).2).trans ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [norm_mul, hact.2]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hF.2.2.1 σ hσ a b).2).trans (norm_le_pi_norm y b)
end GlobalTheory.Cyc.Procyclic
