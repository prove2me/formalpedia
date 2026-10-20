-- Prove2me | solution 1 for OAI.LipschitzCounterexample.Criterion.assemble
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:11:06.151979+00:00
-- url     : https://prove2.me/submissions/d43f37fa-8e5c-4658-b524-5eaffeaad4c0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/BanachAssembly.lean:L46-L84
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.Criterion.assemble. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Theorems.Thm_OAI_LipschitzCounterexample_GraphObstruction_graph_no_c0L2
import Theorems.Thm_OAI_LipschitzCounterexample_WeightedGraph_lipschitz_lift

-- ---- from OAI.Analysis.LipschitzEquivalence.GraphEmbedding ----
namespace OAI

universe uU uV

noncomputable section
namespace LipschitzCounterexample

namespace Criterion
open scoped NNReal ENNReal Topology
open Filter
variable {U : Type uU} {V : Type uV} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (q : Free U V →L[ℝ] U) (h : Domain U V ≃ U)
  (hlin : ∀ x : Domain U V, q (FreeSpace.point x) = h x - x.fst)
  (h0 : h 0 = 0) {a b : ℝ≥0} (hh : LipschitzWith b h) (hi : LipschitzWith a h.symm)

theorem lipschitz_graphEquiv : LipschitzWith (max (1 + max ‖q‖₊ 1) b)
    (graphEquiv q h hlin h0 hh hi) :=
  WeightedGraph.lipschitz_lift (Q1 q) q (B q) h (lipschitz_B q) hh
    (B_zero q) h0 (diagram q h hlin)

theorem lipschitz_graphEquiv_symm : LipschitzWith (max (1 + 2 * ‖q‖₊ * a) a)
    (graphEquiv q h hlin h0 hh hi).symm :=
  WeightedGraph.lipschitz_lift q (Q1 q) (Binv q h) h.symm (lipschitz_Binv q h hi) hi
    (Binv_zero q h h0) (symm_zero h h0) (Q1_Binv q h hlin)

end Criterion

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.BanachAssembly ----
namespace OAI

universe uE uX uY

noncomputable section

namespace LipschitzCounterexample
namespace Criterion
open WeakSequences
open scoped NNReal

theorem contains_of_isometry_equiv {E : Type uE} {X : Type uX} {Y : Type uY} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : E →ₗᵢ[ℝ] X) (e : X ≃L[ℝ] Y) : ContainsLinearCopy E Y := by
  refine ⟨e.toContinuousLinearMap.comp j.toContinuousLinearMap, 1/(‖e.symm.toContinuousLinearMap‖+1),
    by positivity, ?_⟩
  intro z
  have he := e.symm.toContinuousLinearMap.le_opNorm (e (j z))
  change ‖e.symm (e (j z))‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (j z)‖ at he
  simp only [e.symm_apply_apply, j.norm_map] at he
  change 1/(‖e.symm.toContinuousLinearMap‖+1)*‖z‖ ≤ ‖e (j z)‖
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < ‖e.symm.toContinuousLinearMap‖+1)).2
  nlinarith [norm_nonneg (e (j z))]

theorem assemble {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U]
    (q : Free U RealL2 →L[ℝ] U)
    (h : Domain U RealL2 ≃ U)
    (hlin : ∀ x : Domain U RealL2, q (FreeSpace.point x) = h x - x.fst)
    (h0 : h 0 = 0)
    (hh : LipschitzWith (26/25) h) (hi : LipschitzWith (25/24) h.symm)
    (hq : ‖q‖ ≤ 51/25)
    (hA : WeakSequentiallyComplete (Free U RealL2))
    (hcc : CompletelyContinuous q) : MainClaim := by
  let X : SeparableRealBanach := { Carrier := WeightedGraph.Space (Q1 q) }
  let Y : SeparableRealBanach := { Carrier := WeightedGraph.Space q }
  let Ψ : X.Carrier ≃ Y.Carrier := graphEquiv q h hlin h0 hh hi
  have hno : ¬ ContainsLinearCopy C0L2 Y.Carrier := by
    rintro ⟨S, a, ha, hS⟩
    exact GraphObstruction.graph_no_c0L2 q hA hcc S a ha hS
  refine ⟨X, Y, Ψ, ?_, ?_, ⟨c0Embed q⟩, hno⟩
  · have hb : max (1 + max ‖q‖₊ 1) (26/25) ≤ (76/25 : ℝ≥0) := by
      have hmax : max ‖q‖ 1 ≤ (51/25 : ℝ) := max_le hq (by norm_num)
      have hr : max (1 + max ‖q‖ 1) (26/25) ≤ (76/25 : ℝ) :=
        max_le (by linarith) (by norm_num)
      exact_mod_cast hr
    have ha : max (1+2*‖q‖₊*(25/24)) (25/24) ≤ (21/4 : ℝ≥0) := by
      have hr : max (1+2*‖q‖*(25/24)) (25/24) ≤ (21/4 : ℝ) :=
        max_le (by linarith) (by norm_num)
      exact_mod_cast hr
    have hf := (lipschitz_graphEquiv q h hlin h0 hh hi).weaken hb
    have hg := (lipschitz_graphEquiv_symm q h hlin h0 hh hi).weaken ha
    intro s t
    have hf' := hf.norm_sub_le s t
    have hg' := hg.norm_sub_le (Ψ s) (Ψ t)
    change ‖Ψ.symm (Ψ s)-Ψ.symm (Ψ t)‖ ≤ (21/4 : ℝ≥0) * ‖Ψ s-Ψ t‖ at hg'
    simp only [Equiv.symm_apply_apply] at hg'
    change ‖Ψ s-Ψ t‖ ≤ (76/25 : ℝ≥0) * ‖s-t‖ at hf'
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat] at hf' hg'
    constructor
    · linarith
    · exact hf'
  · refine ⟨fun e => hno (contains_of_isometry_equiv (c0Embed q) e)⟩

end Criterion
end LipschitzCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.Criterion
open WeakSequences
open scoped NNReal


theorem solution : type_of% @_root_.OAI.LipschitzCounterexample.Criterion.assemble := @_root_.OAI.LipschitzCounterexample.Criterion.assemble
