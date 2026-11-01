-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:25:35.706525+00:00
-- url     : https://prove2.me/submissions/f619ac0f-d730-4dc3-a5b3-d564aa4185ee

import Mathlib
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K042
import Theorems.Thm_OAI_MetricKMedian_PCP_ExpanderFamily_graph_contracts_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

theorem propagate_mean (n : ℕ) (f : V → ℝ) :
    (𝔼 v, G.propagate n f v) = 𝔼 v, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, adjacency_mean, ih]

theorem propagate_contract {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f : V → ℝ) (hf : (𝔼 v, f v) = 0) :
    energy (G.propagate n f) ≤ ρ^(2*n) * energy f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      energy (G.propagate (n+1) f) ≤ ρ^2 * energy (G.propagate n f) :=
        hG _ ((G.propagate_mean n f).trans hf)
      _ ≤ ρ^2 * (ρ^(2*n) * energy f) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ρ^(2*(n+1)) * energy f := by rw [show 2*(n+1)=2+2*n by omega, pow_add]; ring

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphProducts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphProducts

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma square_adjacency (G : PortGraph V D) (f : V → ℝ) :
    G.square.adjacency f=G.adjacency (G.adjacency f) := by
  funext v
  unfold adjacency
  simp_rw [square_step]
  exact expect_prod _

omit [Nonempty V] in
theorem square_contracts (G : PortGraph V D) {ρ : ℝ} (h : G.Contracts ρ) :
    G.square.Contracts (ρ^2) := by
  intro f hf
  rw [square_adjacency]
  have hh := G.propagate_contract h 2 f hf
  simpa only [propagate_succ,propagate_zero,show 2*2=4 by decide,← pow_mul] using hh

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphProducts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_GlobalRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGlobalRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace GlobalRegularization
variable {V E A : Type} [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

omit [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma strong_contracts_s53_oai : (strong C).Contracts (1/16) := by
  have h := ((ExpanderFamily.graph (depth C)).square).square_contracts
    ((ExpanderFamily.graph (depth C)).square_contracts (ExpanderFamily.graph_contracts_s53 _))
  norm_num at h
  exact h

end GlobalRegularization
end MetricKMedian.PCP

end Inline_PCPGlobalRegularization

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53_oai := @OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53_oai
