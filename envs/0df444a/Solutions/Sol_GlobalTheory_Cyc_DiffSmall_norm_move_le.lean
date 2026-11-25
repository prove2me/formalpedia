-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.norm_move_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:39:24.724825+00:00
-- url     : https://prove2.me/submissions/e54400ce-1261-4846-81cc-c2f6c57c8704

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
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_gal
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_add_le_of_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sum_le_of_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_pow_sub_pow_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_root
import Theorems.Thm_GlobalTheory_T_integers_eq_sum_zeta_pow_unique


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
theorem _root_.solution (K : FinExt l) {τ : GQ l} (hτ : τ ∈ Gj K 1) (i : ℕ) (hi : 1 ≤ i) :
    ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → ∀ z ∈ Ks K i, ‖z‖ ≤ 1 → ‖τ z - z‖ ≤ ‖τ ζ - ζ‖ := by
  have hl : l.Prime := Fact.out
  induction i, hi using Nat.le_induction with
  | base =>
    intro ζ _ z hz _
    have : τ z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ z hz
    simp [this]
  | succ i hi ih =>
    intro ζ hζ z hz hn
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K (i + 1) (by omega) ζ hζ).1 z hz hn
    have hζ1 : ‖ζ‖ ≤ 1 := (norm_root (pow_ne_zero _ hl.ne_zero) hζ.pow_eq_one).le
    have hτ1 : ‖τ ζ‖ ≤ 1 := by rwa [norm_gal]
    have hζ' : IsPrimitiveRoot (ζ ^ l) (l ^ i) :=
      hζ.pow (pow_pos hl.pos _) (by ring)
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine norm_sum_le_of_le _ _ (norm_nonneg _) fun a _ => ?_
    have : τ (ζ ^ (a : ℕ) * y a) - ζ ^ (a : ℕ) * y a =
        τ ζ ^ (a : ℕ) * (τ (y a) - y a) + y a * (τ ζ ^ (a : ℕ) - ζ ^ (a : ℕ)) := by
      rw [map_mul, map_pow]; ring
    rw [this]
    refine norm_add_le_of_le ?_ ?_
    · rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hτ1)).trans ?_
      refine (ih _ hζ' _ (by simpa using (hy a).1) (hy a).2).trans ?_
      rw [map_pow]
      exact norm_pow_sub_pow_le hτ1 hζ1 _
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hy a).2).trans (norm_pow_sub_pow_le hτ1 hζ1 _)
end GlobalTheory.Cyc.DiffSmall
