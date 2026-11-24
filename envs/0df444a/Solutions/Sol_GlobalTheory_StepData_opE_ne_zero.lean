-- Prove2me | solution 1 for GlobalTheory.StepData.opE_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:55:56.594158+00:00
-- url     : https://prove2.me/submissions/e7c107c0-3229-4bfe-aef7-1688f0078d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.StepData
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = 1 ∧ IntM x) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by
  classical
  have := secondCountable k
  have := t2Space k
  have hc : Continuous (affPt (c := c) p x₀) := by
    refine continuous_const.add (continuous_pi fun r => continuous_pi fun s => ?_)
    by_cases hf : Free p (r, s)
    · simp only [Matrix.of_apply, dif_pos hf]; exact continuous_apply _
    · simp only [Matrix.of_apply, dif_neg hf]; exact continuous_const
  have key : ∀ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) = (‖Φ (affPt p x₀ e)‖ : ℝ) := fun e => by
    by_cases h : Φ (affPt p x₀ e) = 0
    · simp [h]
    · obtain ⟨h1, h2⟩ := h01 _ h
      have hi : -ch (affPt p x₀ e) ∈ 𝒪[k] := neg_mem (sum_mem fun i _ => h2 _ _)
      rw [h1, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]; simp
  unfold opE
  simp only [key]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hΦ.1.continuous.comp hc).norm ?_
    (fun _ => norm_nonneg _) (x := e₀) (norm_ne_zero_iff.2 he)).ne'
  refine HasCompactSupport.intro (isCompact_univ_pi fun rs => (isCompact_int k).image
    (continuous_sub_right (basePt c x₀ rs.1.1 rs.1.2))) fun e he' => norm_eq_zero.2 (by_contra fun h => he' ?_)
  rintro ⟨⟨r, s⟩, hf⟩ -
  exact ⟨_, (h01 _ h).2 r s, by simp [affPt, hf]⟩
end GlobalTheory.StepData
