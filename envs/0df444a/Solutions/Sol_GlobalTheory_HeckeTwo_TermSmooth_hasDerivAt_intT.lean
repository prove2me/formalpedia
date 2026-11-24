-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_intT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:36.325809+00:00
-- url     : https://prove2.me/submissions/f124a0df-6e8b-48c8-90ea-33a8b5c9c87a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_hasDerivAt_term
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_continuous_term
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_norm_term_le
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_ne_zero_of_mem_ball
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_integrable_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) :
    HasDerivAt (intT σ ν a b m)
      (-(a : ℂ) * I * intT σ ν (a + 1) b m y₀ + 2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀
        + (m : ℂ) * intT σ ν a b (m - 1) y₀) y₀ := by
  obtain ⟨b1, hb1, h1⟩ := norm_term_le σ hσ ν (a + 1) b m (by omega) hy₀
  obtain ⟨b2, hb2, h2⟩ := norm_term_le σ hσ ν a (b + 1) (m + 1) (by omega) hy₀
  obtain ⟨b3, hb3, h3⟩ := norm_term_le σ hσ ν a b (m - 1) hab hy₀
  have i1 := integrable_term σ hσ ν m (a := a + 1) (b := b) (by omega) hy₀
  have i2 := integrable_term σ hσ ν (m + 1) (a := a) (b := b + 1) (by omega) hy₀
  have i3 := integrable_term σ hσ ν (m - 1) (a := a) (b := b) hab hy₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y t => term σ ν a b m y t)
    (F' := fun y t => -(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t)
    (bound := fun t => ‖-(a : ℂ) * I‖ * b1 t + ‖2 * (-σ - (b : ℂ))‖ * b2 t + ‖(m : ℂ)‖ * b3 t)
    (Metric.ball_mem_nhds y₀ (by positivity))
    (Filter.eventually_of_mem (isOpen_ne.mem_nhds hy₀) fun y hy => (continuous_term σ ν a b m hy).aestronglyMeasurable)
    (integrable_term σ hσ ν m hab hy₀)
    ((((continuous_term σ ν _ _ _ hy₀).const_mul _).add ((continuous_term σ ν _ _ _ hy₀).const_mul _)).add
      ((continuous_term σ ν _ _ _ hy₀).const_mul _)).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t y hy => by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
        rw [norm_mul] <;> gcongr
      · exact h1 t y hy
      · exact h2 t y hy
      · exact h3 t y hy)
    (((hb1.const_mul _).add (hb2.const_mul _)).add (hb3.const_mul _))
    (MeasureTheory.ae_of_all _ fun t y hy => hasDerivAt_term σ ν a b m (ne_zero_of_mem_ball hy₀ hy) t)
  have k2 := key.2
  have hI : (∫ t, (-(a : ℂ) * I * term σ ν (a + 1) b m y₀ t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y₀ t
        + (m : ℂ) * term σ ν a b (m - 1) y₀ t)) = -(a : ℂ) * I * intT σ ν (a + 1) b m y₀ +
        2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀ + (m : ℂ) * intT σ ν a b (m - 1) y₀ := by
    unfold intT
    rw [MeasureTheory.integral_add _ (i3.const_mul _), MeasureTheory.integral_add (i1.const_mul _) (i2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact (i1.const_mul _).add (i2.const_mul _)
  rw [hI] at k2
  exact k2
end GlobalTheory.HeckeTwo.TermSmooth
