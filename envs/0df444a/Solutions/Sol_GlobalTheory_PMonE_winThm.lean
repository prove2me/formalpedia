-- Prove2me | solution 1 for GlobalTheory.PMonE.winThm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:36.645975+00:00
-- url     : https://prove2.me/submissions/3a0bc1c2-2c6d-483f-9b28-ab5853d59dd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWindowRadii
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrdersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMonoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPolydiscWindowsSurjectiveBoundsZero
import Theorems.Thm_GlobalTheory_PMonE_normalize
import Theorems.Thm_GlobalTheory_PMonE_exists_window_radii
import Theorems.Thm_GlobalTheory_PMonE_rowT_eq_rowS
import Theorems.Thm_GlobalTheory_T_additiveSystem_generalLemma_all_orders
import Theorems.Thm_GlobalTheory_T_card_windowZeros_eq_integral_additiveSystem
import Theorems.Thm_GlobalTheory_T_card_windowZeros_inner_eq_shifted_outer
import Theorems.Thm_GlobalTheory_T_frobeniusWindowSeriesTerm_norm_le_rowBound
import Theorems.Thm_GlobalTheory_T_norm_frobeniusWindowSeriesTerm_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
namespace GlobalTheory.PMonE
theorem _root_.solution : WinThm := by
  intro F _ _ _ _ p _ _ _ h ϖ hh hϖ lam hlam hanti horth hlt
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨π, hπ, hrel1, hrel2⟩ := exists_window_radii F p k ϖ hϖ lam hlam hanti hlt
  have hp := (Fact.out : p.Prime)
  have hϖ0 : ϖ ≠ 0 := by
    have : (0 : ℝ) < ‖ϖ‖ := by
      rw [hϖ]
      exact inv_pos.2 (by exact_mod_cast hp.pos)
    exact norm_pos_iff.1 this
  have hbd := GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound F p k ϖ hϖ lam π hlam hanti hlt hπ hrel1 hrel2
  have hb : ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) :=
    fun r j n => ⟨(hbd r j n).1, (hbd r j n).2.1⟩
  have hπ0 : ∀ j, π j ≠ 0 := fun j => (hπ j).1
  have hGL := GlobalTheory.T.additiveSystem_generalLemma_all_orders
  refine ⟨fun j => ‖π j‖, fun r => ‖lam r * π r ^ p ^ (r : ℕ)‖, 2,
    fun j => ⟨norm_pos_iff.2 (hπ j).1, (hπ j).2⟩,
    fun r => norm_pos_iff.2 (mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r).1)), ?_, ?_, ?_⟩
  · intro x hx r j n
    have hm := GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono F p (k + 1) ϖ lam π x hx r j n
    exact ⟨hm.trans (hbd r j n).1, fun hn => hm.trans ((hbd r j n).2.2 (by exact_mod_cast hn))⟩
  · intro b hbnd
    obtain ⟨M, hM, _, Φ, hΦ, _, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨z, hz, hzb⟩ := (hGL 2).1 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM (Φ b)
      (hΦ b hbnd)
    refine ⟨winPt p π 2 z, ?_, fun r => ?_⟩
    · intro j
      simp only [winPt]
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz j))
    · rw [rowT_eq_rowS]
      exact (hiff z b).1 hzb r
  · obtain ⟨M, hM, hM0, Φ, _, hΦ0, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨M', hM', hM0', Φ', _, hΦ0', hiff'⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth (2 - 1) (2 + 1) (by norm_num) hb
    have c1 := (hGL 2).2 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM hM0
    have c2 := (hGL (2 - 1)).2 F p (Fin (k + 1)) (k + 1) ((2 - 1) + (2 + 1)) (by omega) (by omega) M' hM' hM0'
    have d1 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 2 2 M (fun z => by simpa [hΦ0] using hiff z 0)
    have d2 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 (2 - 1) (2 + 1) M' (fun z => by simpa [hΦ0'] using hiff' z 0)
    have e1 := GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer F p (k + 1) 2 ϖ hϖ0 (by norm_num) lam π
    have hq1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    have cS : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =
        (p ^ (k + 1)) ^ ((k + 1) * 2) := by
      rw [d1, c1, Fintype.card_fin]
    have cI : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} = (p ^ (k + 1)) ^ ((k + 1) * (2 - 1)) := by
      rw [e1, d2, c2, Fintype.card_fin]
    by_contra hcon
    have hsub : ∀ x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0},
        ∀ j, ‖x.1 j‖ ≤ ‖π j‖ ^ p ^ (k + 1) := by
      intro x
      by_contra hx
      push_neg at hx
      exact hcon ⟨x.1, x.2.1, hx, x.2.2⟩
    haveI : Finite {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} := Nat.finite_of_card_ne_zero (by rw [cI]; positivity)
    have hle := Nat.card_le_card_of_injective
      (fun x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =>
        (⟨x.1, hsub x, x.2.2⟩ : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
          ∀ r, rowT p ϖ lam 2 x r = 0}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [cS, cI] at hle
    exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hq1 (by omega)))
end GlobalTheory.PMonE
