-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.norm_l_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:07.615248+00:00
-- url     : https://prove2.me/submissions/ebd65845-44b9-40d5-8ab7-285fe74cb9d4

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
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sub_le_one
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_pow_sub_pow_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_root
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_prod_norm_one_sub

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
theorem _root_.solution (j : ℕ) : ∀ η : Om l, η ^ l ^ j = 1 → η ≠ 1 → ‖(l : Om l)‖ ≤ ‖1 - η‖ := by
  have hl : l.Prime := Fact.out
  induction j with
  | zero => intro η h h1; simp at h; exact absurd h h1
  | succ j ih =>
    intro η h h1
    have hη : ‖η‖ ≤ 1 := (norm_root (pow_ne_zero _ hl.ne_zero) h).le
    have hb : ∀ a : ℕ, ‖1 - η ^ a‖ ≤ ‖1 - η‖ := fun a => by
      simpa using norm_pow_sub_pow_le (u := (1 : Om l)) (by simp) hη a
    by_cases h2 : η ^ l = 1
    · have hp : IsPrimitiveRoot η l := by
        have := orderOf_eq_prime h2 h1
        have h3 := IsPrimitiveRoot.orderOf η
        rwa [this] at h3
      rw [← prod_norm_one_sub hl.pos hp]
      obtain ⟨m, hm⟩ : ∃ m, l - 1 = m + 1 := ⟨l - 2, by have := hl.two_le; omega⟩
      rw [hm, Finset.prod_range_succ]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb _)
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ =>
        (hb _).trans (norm_sub_le_one (by simp) hη)
    · exact (ih (η ^ l) (by rw [← pow_mul, ← h]; ring) h2).trans (hb _)
end GlobalTheory.Cyc.DiffSmall
