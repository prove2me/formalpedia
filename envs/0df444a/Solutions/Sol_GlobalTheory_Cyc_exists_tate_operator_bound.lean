-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_tate_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:53.481167+00:00
-- url     : https://prove2.me/submissions/7224a61a-2df1-4489-81e7-e56b34e8fbaa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_le
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_zeta_sub_one_mem
import Theorems.Thm_GlobalTheory_Cyc_TateS_est
import Theorems.Thm_GlobalTheory_Cyc_TateS_solve
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open TateS
namespace GlobalTheory.Cyc
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∃ S : PadicComplex l → PadicComplex l, (∀ x ∈ Xj K j, S x ∈ Xj K j ∧ ‖S x‖ ≤ (l : ℝ) * ‖x‖ ∧ act g (S x) - S x = (ζ - 1) * x ∧ S (act g x - x) = (ζ - 1) * x) ∧ (∀ x ∈ Xj K j, ∀ x' ∈ Xj K j, S (x + x') = S x + S x') ∧ ∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, S (y * x) = y * S x := by
  classical
  intro l _ act χ hact hχ K j hj g hg ζ hζ
  have hp : l.Prime := Fact.out
  have T1 := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))
  have hz := zeta_sub_one_mem K hj.1 hζ
  have hex : ∀ x, ∃ y, x ∈ Xj K j → y ∈ Xj K j ∧ act g y - y = (ζ - 1) * x := by
    intro x
    by_cases hx : x ∈ Xj K j
    · obtain ⟨y, hy⟩ := solve hact hχ K hj hg hζ hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose S hS using hex
  have huniq : ∀ x ∈ Xj K j, ∀ y ∈ Xj K j, act g y - y = (ζ - 1) * x → S x = y := by
    intro x hx y hy h
    have h1 := est hact hχ K hj hg hζ (sub_mem (hS x hx).1 hy)
    have h2 : act g (S x - y) - (S x - y) = 0 := by
      rw [map_sub]; linear_combination (hS x hx).2 - h
    rw [h2, norm_zero, mul_zero] at h1
    have h3 : ‖S x - y‖ ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.2 (mul_pos hζ1 (not_le.1 hc)))
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h3)
  refine ⟨S, fun x hx => ⟨(hS x hx).1, ?_, (hS x hx).2, ?_⟩, fun x hx x' hx' => ?_,
    fun y hy x hx => ?_⟩
  · have h1 := est hact hχ K hj hg hζ (hS x hx).1
    rw [(hS x hx).2, norm_mul, mul_left_comm] at h1
    exact le_of_mul_le_mul_left h1 hζ1
  · refine huniq _ (sub_mem (T1.2.2.2.2.1 g (Gj_le K j hg.1) x hx) hx) _ (T1.2.2.2.1 _ hz x hx) ?_
    rw [map_mul, act_fix hact K hg.1 hz.1]
    ring
  · refine huniq _ (add_mem hx hx') _ (add_mem (hS x hx).1 (hS x' hx').1) ?_
    rw [map_add]
    linear_combination (hS x hx).2 + (hS x' hx').2
  · refine huniq _ (T1.2.2.2.1 y hy x hx) _ (T1.2.2.2.1 y hy _ (hS x hx).1) ?_
    rw [map_mul, act_fix hact K hg.1 hy.1]
    linear_combination y * (hS x hx).2
end GlobalTheory.Cyc
