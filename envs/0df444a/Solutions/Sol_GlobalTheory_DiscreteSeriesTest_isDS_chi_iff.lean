-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.isDS_chi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:48.838669+00:00
-- url     : https://prove2.me/submissions/dd07f7e1-d149-41c2-9511-f2f682daf20e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_norm_entry
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_wt_eq
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_lowK_one
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_compact_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest
namespace GlobalTheory.DiscreteSeriesTest
theorem _root_.solution (ε : Fin 1 → Bool) (m : ℤ) (lam : Fin 1 → ℝ) :
    IsDS ε lam (chi m) ↔ lam = fun _ => (m : ℝ) := by
  constructor
  · rintro ⟨-, -, -, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩
    rw [← wt_eq m _ v hv0 hv, lowK_one]
  rintro rfl
  have hsub : ∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤ := fun S => eq_bot_or_eq_top S
  have hiso : ∀ g ∈ UJset ε, ∀ v : ℂ, ‖chi m g v‖ = ‖v‖ := by
    intro g hg v
    simp [chi, norm_zpow, norm_entry hg]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, ?_⟩, hiso, ?_⟩, fun S _ _ => hsub S, ?_, ⟨⊤, ?_⟩, ?_⟩
  · ext; simp [chi]
  · intro a _ b _
    ext
    simp [chi, Matrix.mul_apply, mul_zpow, mul_comm]
  · intro v
    simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (by fun_prop) m ?_) continuousOn_const
    intro g hg
    left
    intro h0
    have := norm_entry hg
    simp [h0] at this
  · intro v w
    have := compact_one ε
    have hfin : IsFiniteMeasure (muG ε) := CompactSpace.isFiniteMeasure
    have hc : Continuous (coefOn (ε := ε) (chi m) v w) := by
      unfold coefOn
      simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      refine Continuous.inner continuous_const (Continuous.mul (Continuous.zpow₀ ?_ m ?_) continuous_const)
      · exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0
      · intro g
        left
        intro h0
        have := norm_entry g.2
        simp [umat] at h0
        simp [h0] at this
    refine MemLp.of_bound hc.aestronglyMeasurable (‖w‖ * ‖v‖) (Filter.Eventually.of_forall fun g => ?_)
    have := norm_inner_le_norm (𝕜 := ℂ) w (chi m (umat g) v)
    rw [hiso _ g.2] at this
    exact this
  · rw [lowK_one]
    refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ _ => hsub S, ⟨1, trivial, one_ne_zero, ?_⟩, ?_⟩
    · intro θ _
      simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, ← Complex.exp_int_mul]
      congr 2
      push_cast; ring
    · intro μ v _ hv h
      rw [wt_eq m μ v hv h]
      exact ⟨fun _ _ => 0, by simp, by simp⟩
  · intro μ S hS
    obtain ⟨v, _, hv, h⟩ := hS.2.2.2.1
    rw [wt_eq m μ v hv h, lowK_one]
end GlobalTheory.DiscreteSeriesTest
