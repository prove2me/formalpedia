-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:16.958574+00:00
-- url     : https://prove2.me/submissions/4f362846-6647-4412-a471-2db54f399def

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_add_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution {u v : Om l} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (a : ℕ) :
    ‖u ^ a - v ^ a‖ ≤ ‖u - v‖ := by
  induction a with
  | zero => simp
  | succ a ih =>
    have : u ^ (a + 1) - v ^ (a + 1) = u * (u ^ a - v ^ a) + v ^ a * (u - v) := by ring
    rw [this]
    refine norm_add_le_of_le ?_ ?_
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans ih
    · rw [norm_mul, norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv)
end GlobalTheory.Cyc.DiffSmall
