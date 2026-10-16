-- Prove2me | solution 1 for OAI.RandomKSAT.variance_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:42:37.610549+00:00
-- url     : https://prove2.me/submissions/6898b8fe-567e-403f-bc06-aedd6cf03ca4

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/CapBridge.lean:L134-L153
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.variance_bridge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge

-- ---- from OAI.Probability.SATVariance.CapBridge ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma variance_bridge.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    variance f μ ≤ 2*variance g μ + 2*(∫ ω, (f ω-g ω)^2 ∂μ) := by
  let c := ∫ ω, g ω ∂μ
  have hfc := hf.sub (memLp_const c)
  have hgc := hg.sub (memLp_const c)
  have hfg := hf.sub hg
  have hv := variance_le_expectation_sq hfc.aestronglyMeasurable
  simp only [Pi.sub_apply, Pi.pow_apply] at hv
  change variance (fun ω => f ω-c) μ ≤ (∫ ω, (f ω-c)^2 ∂μ) at hv
  rw [variance_sub_const hf.aestronglyMeasurable] at hv
  have hm := integral_mono hfc.integrable_sq
    ((hgc.integrable_sq.const_mul 2).add (hfg.integrable_sq.const_mul 2))
    (fun ω => by dsimp; nlinarith [sq_nonneg ((f ω-g ω)-(g ω-c))])
  change (∫ ω, (f ω-c)^2 ∂μ) ≤ (∫ ω, 2*(g ω-c)^2+2*(f ω-g ω)^2 ∂μ) at hm
  have hgi : Integrable (fun ω => (g ω-c)^2) μ := hgc.integrable_sq
  have hfgi : Integrable (fun ω => (f ω-g ω)^2) μ := hfg.integrable_sq
  rw [integral_add (hgi.const_mul 2) (hfgi.const_mul 2),
    integral_const_mul, integral_const_mul, ← variance_eq_integral hg.aemeasurable] at hm
  exact hv.trans hm

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.variance_bridge := @_root_.OAI.RandomKSAT.variance_bridge
