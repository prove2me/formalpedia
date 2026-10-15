-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:41:44.982449+00:00
-- url     : https://prove2.me/submissions/cd1011f3-485f-439a-8bae-722da1fb53e8

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Termination.lean:L37-L63
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget

-- ---- from OAI.Probability.Localization.Termination ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

open Filter
open scoped Topology

lemma frozen_nonnegative_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f : ℕ → α → ℝ) (F : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ N,Integrable (f N) P) (hf0 : ∀ N z,0 ≤ f N z)
    (hF : AEStronglyMeasurable F P) (hF0 : ∀ z,0 ≤ F z)
    (hfreeze : ∀ᵐ z ∂P,∃ N,∀ M,N ≤ M → f M z = F z)
    (hbound : ∀ N,(∫ z,f N z ∂P) ≤ B) :
    Integrable F P ∧ (∫ z,F z ∂P) ≤ B := by
  have he : (fun z => ENNReal.ofReal (F z)) =ᵐ[P]
      (fun z => liminf (fun N => ENNReal.ofReal (f N z)) atTop) := by
    filter_upwards [hfreeze] with z hz
    obtain ⟨N,hN⟩ := hz
    have ht : Tendsto (fun M => ENNReal.ofReal (f M z)) atTop (𝓝 (ENNReal.ofReal (F z))) :=
      tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N,fun M hM => congrArg ENNReal.ofReal (hN M hM).symm⟩)
    exact ht.liminf_eq.symm
  have hb : (∫⁻ z,ENNReal.ofReal (F z) ∂P) ≤ ENNReal.ofReal B := by
    rw [lintegral_congr_ae he]
    apply (lintegral_liminf_le' (fun N => (hf N).aemeasurable.ennreal_ofReal)).trans
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall (fun N => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf N) (ae_of_all _ (hf0 N))]
      exact ENNReal.ofReal_le_ofReal (hbound N))
  have hi : Integrable F P := ⟨hF,(hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)).mpr
    (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hF0)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Filter
open scoped Topology

theorem solution {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f : ℕ → α → ℝ) (F : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ N,Integrable (f N) P) (hf0 : ∀ N z,0 ≤ f N z)
    (hF : AEStronglyMeasurable F P) (hF0 : ∀ z,0 ≤ F z)
    (hfreeze : ∀ᵐ z ∂P,∃ N,∀ M,N ≤ M → f M z = F z)
    (hbound : ∀ N,(∫ z,f N z ∂P) ≤ B) :
    Integrable F P ∧ (∫ z,F z ∂P) ≤ B := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound P f F B hB hf hf0 hF hF0 hfreeze hbound
    | exact OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound
    | (apply OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound <;> assumption)
