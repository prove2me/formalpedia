-- Prove2me | solution 1 for GlobalTheory.RealWeil.sm_superpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:29.05698+00:00
-- url     : https://prove2.me/submissions/599e554c-0c5f-467f-a017-14016f8fa93f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
import Theorems.Thm_GlobalTheory_RealWeil_Superpos_contDiff_int
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by
  intro V Y _ _ _ _ _ _ _ _ ν B _ _ _ om ρ hom hρ ι c hc hm f hf
  have skew : ∀ v w, om w v = -om v w := by
    intro v w
    have := hom (v + w)
    simp only [map_add, ContinuousLinearMap.add_apply, hom] at this
    linarith
  have comm : ∀ v w b, ρ v (ρ w b) = cexp (2 * π * I * (om v w : ℂ)) • ρ w (ρ v b) := by
    intro v w b
    rw [hρ.2.1 v w, hρ.2.1 w v, smul_smul, ← Complex.exp_add, add_comm w v]
    simp only [skew v w]
    congr 2
    push_cast
    ring
  have hint : Integrable (fun y => c y • ρ (ι y) f) ν := by
    refine Integrable.mono' ((hm 0).mul_const ‖f‖) (hc.smul ((hρ.2.2.2 f).comp ι.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp [norm_smul, hρ.2.2.1]
  have e : (fun v => ρ v (∫ y, c y • ρ (ι y) f ∂ν)) =
      fun v => ∫ y, Superpos.itg om ρ ι c (fun w => ρ w f) v y ∂ν := by
    funext v
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Superpos.itg, Superpos.ph, map_smul, comm v (ι y), smul_smul]
  unfold Sm
  rw [e]
  exact contDiff_infty.2 fun n => Superpos.contDiff_int hρ n c ⟨hc, hm⟩ _ hf
end GlobalTheory.RealWeil
