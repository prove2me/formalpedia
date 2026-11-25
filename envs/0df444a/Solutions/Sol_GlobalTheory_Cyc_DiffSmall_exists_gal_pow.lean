-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_gal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:10.30715+00:00
-- url     : https://prove2.me/submissions/f852c299-3740-4d2f-aa66-899ff1d345eb

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
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic
import Theorems.Thm_GlobalTheory_Cyc_exists_isCyc
import Theorems.Thm_GlobalTheory_T_finrank_cyclotomicExt_and_cyclotomicChar_surjective


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
theorem _root_.solution (K : FinExt l) (i m : ℕ) {ζ : Om l} (hζ : ζ ^ l ^ i = 1) :
    ∃ τ ∈ Gj K 1, τ ζ = ζ ^ (1 + l * m) := by
  have hl : l.Prime := Fact.out
  obtain ⟨χ, hχ⟩ := exists_isCyc l
  have hlt : ‖((l * m : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((l * m : ℕ) : ℤ) 1).2 (by simp)
    simpa using this
  have hlt1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by exact_mod_cast hl.one_lt) (by simp)
  have hu : ‖((1 + l * m : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Nat.cast_add, Nat.cast_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one,
      max_eq_left (hlt.trans hlt1.le)]
    rw [norm_one]
    exact (hlt.trans_lt hlt1).ne'
  obtain ⟨g, hg, hgu⟩ := (GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective l K).2 χ hχ _ hu
  refine ⟨g, (((cyc_basic l χ hχ).2.2 K g hg).1 1).2 ?_, ?_⟩
  · rw [hgu, Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
    exact hlt
  · obtain ⟨a, ha, hga⟩ := hχ g i ζ hζ
    rw [hga]
    rw [hgu] at ha
    have hd : ((l : ℤ) ^ i) ∣ ((1 + l * m : ℕ) : ℤ) - (a : ℤ) := by
      rw [← Padic.norm_int_le_pow_iff_dvd]
      simpa using ha
    have hmod : a ≡ 1 + l * m [MOD l ^ i] := (Nat.modEq_iff_dvd).2 (by simpa using hd)
    rw [pow_eq_pow_mod a hζ, pow_eq_pow_mod (1 + l * m) hζ, hmod]
end GlobalTheory.Cyc.DiffSmall
